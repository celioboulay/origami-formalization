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

    # How each huzita_N call needs to be shaped in generated Lean, read
    # directly off its statement in Huzita_axioms.lean:
    #   - "unique": the theorem is `∃!` (needs a trailing `-` to discard the
    #     uniqueness clause) vs a plain `∃`.
    #   - "conjuncts": how many `∧`-joined facts the existence property
    #     itself carries (e.g. huzita_1's `f_through_p f p1 ∧ f_through_p f
    #     p2` is 2) -- this is how many named hypotheses the `obtain`
    #     pattern must destructure, in addition to the witness fold.
    #   - "hypothesis": a side condition (e.g. `p1 ≠ p2`) the call needs
    #     that isn't otherwise derivable from the opaque Point/Line axioms
    #     -- postulated as its own `axiom`, the same way the entities
    #     themselves are postulated rather than proved from literal
    #     coordinates. `None` when the axiom needs no such condition.
    AXIOM_SHAPE: Dict[int, Dict[str, Any]] = {
        1: {"unique": True, "conjuncts": 2,
            "hypothesis": lambda a: f"{a['p1']} ≠ {a['p2']}"},
        2: {"unique": True, "conjuncts": 1,
            "hypothesis": lambda a: f"{a['p1']} ≠ {a['p2']}"},
        3: {"unique": False, "conjuncts": 1, "hypothesis": None},
        4: {"unique": True, "conjuncts": 2, "hypothesis": None},
        5: {"unique": False, "conjuncts": 2,
            "hypothesis": lambda a: f"dist2_line {a['l1']} {a['p2']} ≤ dist2 {a['p1']} {a['p2']}"},
        6: {"unique": False, "conjuncts": 2,
            "hypothesis": lambda a: f"¬ parallel {a['l1']} {a['l2']}"},
        7: {"unique": True, "conjuncts": 2,
            "hypothesis": lambda a: f"¬ parallel {a['l1']} {a['l2']}"},
    }

    def __init__(self, lean_output_path: Union[str, Path, None] = None):
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
        # Reverse of _entity_ids, so an entity produced by an undone axiom
        # can be forgotten in O(1) instead of scanning for its coord key.
        self._id_to_key: Dict[str, tuple] = {}
        self._point_count = 0
        self._line_count = 0
        # When set, the Lean File is kept in sync on every stack mutation
        # (add/undo/clear), per the "continuous write" data flow.
        self.lean_output_path = Path(lean_output_path) if lean_output_path else None

    # ------------------------------------------------------------------
    # Stack management
    # ------------------------------------------------------------------

    def add_axiom(
        self,
        axiom_type: int,
        params: Dict[str, Any],
        produced: Union[Dict[str, Any], None] = None,
    ) -> Dict[str, Any]:
        """
        Validates and adds a Huzita axiom call to the stack.

        `params` are the entities this axiom *depends on* (already
        available before this call). `produced` -- the new crease line
        and any new intersection points the fold makes available -- is
        what this specific axiom *creates*; only those newly-created
        entities are un-declared again if this axiom is later undone.

        Returns a JSON-serializable summary of the axiom as recorded.
        """
        self._validate_axiom(axiom_type, params)
        resolved = {
            name: self._resolve_entity(entity) for name, entity in params.items()
        }
        produced_ids = self._register_produced(axiom_type, produced)
        entry = {
            "type": axiom_type,
            "params": resolved,
            "produced_ids": produced_ids,
            "seq": self._seq,
        }
        self._seq += 1
        self.axioms.append(entry)
        self._sync_lean_file()
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
        (by seq), un-declaring whatever crease/points an undone axiom
        produced (but not the entities it depended on -- those pre-existed
        it and remain available; references never enter self._entities, so
        there is nothing to forget for them). Returns "axiom", "reference",
        or None if both are empty.
        """
        axiom_seq = self.axioms[-1]["seq"] if self.axioms else -1
        ref_seq = self.references[-1]["seq"] if self.references else -1
        if axiom_seq < 0 and ref_seq < 0:
            return None
        if axiom_seq > ref_seq:
            entry = self.axioms.pop()
            for identifier in entry.get("produced_ids", []):
                self._forget_entity(identifier)
            self._sync_lean_file()
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
        self._id_to_key = {}
        self._point_count = 0
        self._line_count = 0
        self._sync_lean_file()

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
        self._id_to_key[identifier] = key
        self._entities[identifier] = dict(entity)
        return identifier

    def _forget_entity(self, identifier: str) -> None:
        """Un-declares an entity, e.g. because the axiom that produced it was undone."""
        self._entities.pop(identifier, None)
        key = self._id_to_key.pop(identifier, None)
        if key is not None:
            self._entity_ids.pop(key, None)

    def _register_produced(
        self, axiom_type: int, produced: Union[Dict[str, Any], None]
    ) -> List[str]:
        """
        Registers the crease line (and any new intersection points) an
        axiom's fold made available, returning only the identifiers that
        were *newly* created by this call -- entities that already existed
        under a previous pick are left untouched and are not returned.
        """
        if not produced:
            return []
        if not isinstance(produced, dict):
            raise ValueError("'produced' must be an object")

        new_ids: List[str] = []

        line = produced.get("line")
        if line is not None:
            entity = dict(line)
            entity["kind"] = "line"
            self._validate_entity(axiom_type, "produced.line", entity, "line")
            before = len(self._entities)
            identifier = self._resolve_entity(entity)
            if len(self._entities) > before:
                new_ids.append(identifier)

        for i, point in enumerate(produced.get("points", [])):
            entity = dict(point)
            entity["kind"] = "point"
            self._validate_entity(axiom_type, f"produced.points[{i}]", entity, "point")
            before = len(self._entities)
            identifier = self._resolve_entity(entity)
            if len(self._entities) > before:
                new_ids.append(identifier)

        return new_ids

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
            "open Origami\n"
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

        side_condition_decls: List[str] = []
        proof_lines: List[str] = []
        for i, axiom in enumerate(self.axioms, start=1):
            axiom_type = axiom["type"]
            params = axiom["params"]
            shape = self.AXIOM_SHAPE[axiom_type]
            arg_names = [params[p] for p in self.AXIOM_ARG_ORDER[axiom_type]]

            if shape["hypothesis"] is not None:
                hyp = f"hyp{i}"
                side_condition_decls.append(f"axiom {hyp} : {shape['hypothesis'](params)}")
                arg_names.append(hyp)

            args = " ".join(arg_names)
            fold_name = f"f{i}"
            lean_axiom = self.AXIOM_LEAN_NAME[axiom_type]

            conjuncts = shape["conjuncts"]
            hyp_names = (
                [f"h{i}"] if conjuncts == 1
                else [f"h{i}{chr(ord('a') + k)}" for k in range(conjuncts)]
            )
            if shape["unique"] and conjuncts > 1:
                # `∃!` unfolds to `∃ x, p x ∧ ∀ y, p y → y = x` -- when `p x`
                # is itself a conjunction (e.g. huzita_1/4/7's property), the
                # full shape is left-nested `(A ∧ B) ∧ uniqueness`, so the
                # compound property needs an explicit inner group; a flat
                # list doesn't match this nesting the way it does for a
                # single-level `∃ x, A ∧ B` (verified against `rcases`).
                items = [fold_name, "⟨" + ", ".join(hyp_names) + "⟩", "-"]
            else:
                items = [fold_name, *hyp_names, *(["-"] if shape["unique"] else [])]
            pattern = ", ".join(items)
            proof_lines.append(f"  obtain ⟨{pattern}⟩ := {lean_axiom} {args}")

        if side_condition_decls:
            lines.append("-- Side conditions the stacked axioms need, that aren't derivable")
            lines.append("-- from the opaque Point/Line axioms above (e.g. two picked points")
            lines.append("-- actually being distinct) -- postulated the same way the picked")
            lines.append("-- geometry itself is postulated.")
            lines.extend(side_condition_decls)
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

    def _sync_lean_file(self) -> None:
        """
        Keeps the Lean File up to date on every stack mutation, so it is
        modified in a continuous flow as axioms are added/undone/cleared
        rather than only once at build time.
        """
        if self.lean_output_path is not None:
            self.write_lean_file(self.lean_output_path)
