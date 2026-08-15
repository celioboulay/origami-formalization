import json
from pathlib import Path
from typing import Any, Dict, List, Union


class OrigamiAPI:
    """
    Manages the state of stacked Huzita axioms and translates them into Lean.

    Each axiom call operates on geometric entities (points / lines) supplied
    by the web interface. Entities are deduplicated by coordinates so that
    picking the same point (or crease) again reuses the same Lean identifier
    across the stack -- this is what lets later axioms build on the
    geometry introduced by earlier ones.
    """

    # Required parameter names per Huzita axiom. The web interface must
    # supply *exactly* this set -- no more, no less.
    AXIOM_REQUIREMENTS: Dict[int, set] = {
        1: {"p1", "p2"},
        2: {"p1", "p2"},
        3: {"l1", "l2"},
        4: {"p1", "l1"},
        5: {"p1", "p2", "l1"},
        6: {"p1", "p2", "l1", "l2"},
        7: {"p1", "l1", "l2"},
    }

    # Lean identifier for the axiom, its declared argument order, and
    # whether it is an `ExistsUnique` (axioms 1-4) or a plain `Exists`
    # (axioms 5-7), which changes the `obtain` pattern needed to use it.
    AXIOM_LEAN_NAME: Dict[int, str] = {
        1: "huzita_1",
        2: "huzita_2",
        3: "huzita_3",
        4: "huzita_4",
        5: "huzita_5",
        6: "huzita_6",
        7: "huzita_7",
    }
    AXIOM_ARG_ORDER: Dict[int, List[str]] = {
        1: ["p1", "p2"],
        2: ["p1", "p2"],
        3: ["l1", "l2"],
        4: ["p1", "l1"],
        5: ["p1", "p2", "l1"],
        6: ["p1", "p2", "l1", "l2"],
        7: ["p1", "l1", "l2"],
    }
    UNIQUE_AXIOMS = {1, 2, 3, 4}

    def __init__(self):
        self.axioms: List[Dict[str, Any]] = []
        # Reference creases: folds whose produced geometry is picked from by
        # later folds but that never enter the Lean-generating axiom stack
        # (see add_reference). Kept in a fully separate list -- their params
        # are never resolved to Lean identifiers, so they cannot leak into
        # generate_lean_code() or self._entities.
        self.references: List[Dict[str, Any]] = []
        # Shared monotonic counter stamped on both axioms and references, so
        # the two lists can be merged back into true chronological order
        # (see describe_stack's "timeline" and undo_last).
        self._seq = 0
        # coordinate-key -> Lean identifier, so repeated picks of the same
        # point/crease resolve to the same variable.
        self._entity_ids: Dict[tuple, str] = {}
        # Lean identifier -> raw entity payload (for codegen + inspection).
        self._entities: "Dict[str, Dict[str, Any]]" = {}
        self._point_count = 0
        self._line_count = 0

    # ------------------------------------------------------------------
    # Stack management
    # ------------------------------------------------------------------

    def add_axiom(self, axiom_type: int, params: Dict[str, Any]) -> Dict[str, Any]:
        """
        Validates and adds a Huzita axiom call to the stack.
        Returns a JSON-serializable summary of the axiom as recorded.
        """
        self._validate_axiom(axiom_type, params)
        resolved = {
            name: self._resolve_entity(entity) for name, entity in params.items()
        }
        entry = {"type": axiom_type, "params": resolved, "seq": self._seq}
        self._seq += 1
        self.axioms.append(entry)
        return self._describe_axiom(len(self.axioms), entry)

    def add_reference(
        self, axiom_type: int, params: Dict[str, Any], produced: Dict[str, Any]
    ) -> Dict[str, Any]:
        """
        Validates and adds a reference crease: a fold whose produced
        geometry (see computeProducedGeometry in main.js) becomes pickable
        for later folds, but that is never resolved into a Lean identifier
        and never appears in generate_lean_code() -- it stays invisible to
        the Lean stack entirely. Returns a JSON-serializable summary.
        """
        self._validate_axiom(axiom_type, params)
        if not isinstance(produced, dict):
            raise ValueError("'produced' must be an object")
        entry = {
            "type": axiom_type,
            "params": dict(params),
            "produced": produced,
            "seq": self._seq,
        }
        self._seq += 1
        self.references.append(entry)
        return self._describe_reference(len(self.references), entry)

    def undo_last(self) -> "str | None":
        """
        Undoes whichever of axioms/references was added most recently
        (by seq). Returns "axiom", "reference", or None if both are empty.
        """
        axiom_seq = self.axioms[-1]["seq"] if self.axioms else -1
        ref_seq = self.references[-1]["seq"] if self.references else -1
        if axiom_seq < 0 and ref_seq < 0:
            return None
        if axiom_seq > ref_seq:
            self.axioms.pop()
            return "axiom"
        self.references.pop()
        return "reference"

    def clear(self) -> None:
        """Clears the axiom stack, reference creases, and all known entities."""
        self.axioms = []
        self.references = []
        self._seq = 0
        self._entity_ids = {}
        self._entities = {}
        self._point_count = 0
        self._line_count = 0

    def describe_stack(self) -> Dict[str, Any]:
        """A JSON-serializable snapshot of the current stack + entities."""
        axioms = [
            self._describe_axiom(i + 1, axiom)
            for i, axiom in enumerate(self.axioms)
        ]
        references = [
            self._describe_reference(i + 1, ref)
            for i, ref in enumerate(self.references)
        ]
        timeline = sorted(
            [{**a, "kind": "axiom"} for a in axioms]
            + [{**r, "kind": "reference"} for r in references],
            key=lambda entry: entry["seq"],
        )
        return {
            "axioms": axioms,
            "references": references,
            "timeline": timeline,
            "entities": dict(self._entities),
            "lean_preview": self.generate_lean_code(),
        }

    def _describe_axiom(self, index: int, entry: Dict[str, Any]) -> Dict[str, Any]:
        return {
            "index": index,
            "type": entry["type"],
            "params": dict(entry["params"]),
            "seq": entry["seq"],
        }

    def _describe_reference(self, index: int, entry: Dict[str, Any]) -> Dict[str, Any]:
        return {
            "index": index,
            "type": entry["type"],
            "params": dict(entry["params"]),
            "produced": entry["produced"],
            "seq": entry["seq"],
        }

    # ------------------------------------------------------------------
    # Validation
    # ------------------------------------------------------------------

    def _validate_axiom(self, axiom_type: int, params: Dict[str, Any]) -> None:
        required = self.AXIOM_REQUIREMENTS.get(axiom_type)
        if required is None:
            raise ValueError(f"Unknown axiom type: {axiom_type}")

        if not isinstance(params, dict):
            raise ValueError("'params' must be an object")

        provided = set(params.keys())
        if provided != required:
            missing = required - provided
            extra = provided - required
            details = []
            if missing:
                details.append(f"missing {sorted(missing)}")
            if extra:
                details.append(f"unexpected {sorted(extra)}")
            required_list = ", ".join(sorted(required))
            raise ValueError(
                f"Axiom {axiom_type} requires exactly {{{required_list}}} "
                f"({'; '.join(details)})"
            )

        for name, entity in params.items():
            expected_kind = "point" if name.startswith("p") else "line"
            self._validate_entity(axiom_type, name, entity, expected_kind)

    @staticmethod
    def _validate_entity(
        axiom_type: int, name: str, entity: Any, expected_kind: str
    ) -> None:
        if not isinstance(entity, dict):
            raise ValueError(f"Axiom {axiom_type}: '{name}' must be an object")
        if entity.get("kind") != expected_kind:
            raise ValueError(
                f"Axiom {axiom_type}: '{name}' must be a {expected_kind} "
                f"(got kind={entity.get('kind')!r})"
            )
        if expected_kind == "point":
            required_fields = ("x", "y")
        else:
            required_fields = ("x1", "y1", "x2", "y2")
        for field in required_fields:
            if field not in entity or not isinstance(entity[field], (int, float)):
                raise ValueError(
                    f"Axiom {axiom_type}: '{name}' is missing numeric field '{field}'"
                )

    # ------------------------------------------------------------------
    # Entity deduplication
    # ------------------------------------------------------------------

    def _resolve_entity(self, entity: Dict[str, Any]) -> str:
        kind = entity["kind"]
        if kind == "point":
            key = ("point", round(entity["x"], 6), round(entity["y"], 6))
        else:
            key = (
                "line",
                round(entity["x1"], 6),
                round(entity["y1"], 6),
                round(entity["x2"], 6),
                round(entity["y2"], 6),
            )

        if key in self._entity_ids:
            return self._entity_ids[key]

        if kind == "point":
            self._point_count += 1
            identifier = f"p{self._point_count}"
        else:
            self._line_count += 1
            identifier = f"l{self._line_count}"

        self._entity_ids[key] = identifier
        self._entities[identifier] = dict(entity)
        return identifier

    # ------------------------------------------------------------------
    # Lean code generation
    # ------------------------------------------------------------------

    def generate_lean_code(self) -> str:
        """
        Generates a Lean script that formally replays the stacked sequence
        of Huzita axiom calls, in order, as a chain of `obtain`s against
        the real `huzita_1` .. `huzita_7` axioms.
        """
        header = (
            "import Origami.lightweight_definitions.Huzita_axioms\n"
            "\n"
            "open scoped Classical\n"
        )

        if not self.axioms:
            return header + "\n-- No axioms in the stack yet.\n"

        lines: List[str] = [header]

        lines.append("-- Geometric entities selected in the web interface")
        for identifier, entity in self._entities.items():
            if entity["kind"] == "point":
                coord = f"({entity['x']:g}, {entity['y']:g})"
                lines.append(f"axiom {identifier} : Point -- picked at {coord}")
            else:
                coord = (
                    f"({entity['x1']:g}, {entity['y1']:g}) -> "
                    f"({entity['x2']:g}, {entity['y2']:g})"
                )
                lines.append(f"axiom {identifier} : Line -- crease {coord}")
        lines.append("")

        nonparallel_decls: List[str] = []
        proof_lines: List[str] = []
        for i, axiom in enumerate(self.axioms, start=1):
            axiom_type = axiom["type"]
            params = axiom["params"]
            arg_names = [params[p] for p in self.AXIOM_ARG_ORDER[axiom_type]]

            if axiom_type == 7:
                hyp = f"hnp{i}"
                nonparallel_decls.append(
                    f"axiom {hyp} : ¬ parallel {params['l1']} {params['l2']}"
                )
                arg_names.append(hyp)

            args = " ".join(arg_names)
            fold_name = f"f{i}"
            hyp_name = f"h{i}"
            lean_axiom = self.AXIOM_LEAN_NAME[axiom_type]

            if axiom_type in self.UNIQUE_AXIOMS:
                proof_lines.append(
                    f"  obtain ⟨{fold_name}, {hyp_name}, -⟩ := {lean_axiom} {args}"
                )
            else:
                proof_lines.append(
                    f"  obtain ⟨{fold_name}, {hyp_name}⟩ := {lean_axiom} {args}"
                )

        if nonparallel_decls:
            lines.append("-- Non-parallel side conditions required by axiom 7")
            lines.extend(nonparallel_decls)
            lines.append("")

        lines.append(f"-- Sequence of {len(self.axioms)} stacked Huzita axiom(s)")
        lines.append("theorem construction : True := by")
        lines.extend(proof_lines)
        lines.append("  trivial")
        lines.append("")

        return "\n".join(lines)

    def write_lean_file(self, output_path: Union[str, Path]) -> None:
        """
        Writes the generated Lean code to a file.
        """
        lean_code = self.generate_lean_code()
        output_path = Path(output_path)
        output_path.parent.mkdir(parents=True, exist_ok=True)
        output_path.write_text(lean_code, encoding="utf-8")
