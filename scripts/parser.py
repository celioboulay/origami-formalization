import argparse
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_INPUT = ROOT / "data" / "simple.json"
DEFAULT_OUTPUT = ROOT / "Origami" / "FOLD" / "parsed.lean"
VALID_EDGE_TYPES = {"V", "M", "F", "U", "B"}

BASE = """import Origami.FOLD.Data.Properties
import Origami.FOLD.Data.WellFormed
import Origami.FOLD.Bridge.DataToMath
set_option linter.style.emptyLine false

noncomputable section
open Origami.FOLD.Bridge

"""


def render_atom(x):
    if isinstance(x, bool):
        raise ValueError("Boolean values are not valid FOLD coordinates")
    if isinstance(x, (int, float)):
        # Keep Lean literals simple and stable.
        if isinstance(x, float) and x.is_integer():
            return str(int(x))
        return str(x)
    if isinstance(x, str):
        return x
    raise ValueError(f"Unsupported JSON value for Lean generation: {x!r}")


def render_list(xs):
    out = []
    for x in xs:
        if isinstance(x, list):
            out.append(render_list(x))
        else:
            out.append(render_atom(x))
    return "[" + ", ".join(out) + "]"


def parse_vertex(i, vertices_coords):
    return f"def v{i} : Vertex := {{coords := {render_list(vertices_coords[i])}}}\n"


def parse_face(i, faces_vertices):
    return f"def f{i} : Face := {{verts := {render_list(faces_vertices[i])}}}\n"


def parse_edge(i, edges_vertices, edges_assignment):
    u, v = edges_vertices[i]
    a = edges_assignment[i]
    return f"def e{i} : Edge := {{u := {u}, v := {v}, assignment := EdgeType.{a}}}\n"


def parse_fold(lv, le, lf):
    vertices = "[" + ", ".join(f"v{i}" for i in range(lv)) + "]"
    edges = "[" + ", ".join(f"e{i}" for i in range(le)) + "]"
    faces = "[" + ", ".join(f"f{i}" for i in range(lf)) + "]"
    return (
        "def F : Fold := {\n"
        f"  vertices := {vertices},\n"
        f"  edges    := {edges},\n"
        f"  faces    := {faces}\n"
        "}\n"
    )


def parse_bridge_block():
    return """
def parsedBridgeReady : Prop :=
  BridgeReady F

def parsedWellFormed2D : Prop :=
  WellFormed2D F

def parsedCreases : List (AffineSubspace Real Point2D) :=
  foldToCreases F

theorem parsedBridgeReady_iff_wellFormed2D :
    parsedBridgeReady ↔ parsedWellFormed2D := by
  simpa [parsedBridgeReady, parsedWellFormed2D] using
    (bridgeReady_iff_wellFormed2D F)

theorem parsedEdgeCrease_exists
    (hReady : parsedBridgeReady) {e : Edge} (he : e ∈ F.edges) :
    ∃ crease : AffineSubspace Real Point2D, edgeToCrease F e = some crease := by
  simpa [parsedBridgeReady] using edgeToCrease_exists_of_bridgeReady (F := F) hReady he

end
"""


def validate_input(data):
    required = ["vertices_coords", "faces_vertices", "edges_vertices", "edges_assignment"]
    for key in required:
        if key not in data:
            raise KeyError(f"Missing key in FOLD JSON: {key}")

    edges_vertices = data["edges_vertices"]
    edges_assignment = data["edges_assignment"]

    if len(edges_assignment) != len(edges_vertices):
        raise ValueError("edges_assignment and edges_vertices must have the same length")

    for i, entry in enumerate(edges_vertices):
        if not isinstance(entry, list) or len(entry) != 2:
            raise ValueError(f"edges_vertices[{i}] must be a pair [u, v]")

    for i, a in enumerate(edges_assignment):
        if a not in VALID_EDGE_TYPES:
            raise ValueError(f"edges_assignment[{i}]={a!r} is invalid")


def generate_lean(data):
    validate_input(data)

    vertices_coords = data["vertices_coords"]
    faces_vertices = data["faces_vertices"]
    edges_vertices = data["edges_vertices"]
    edges_assignment = data["edges_assignment"]

    lv, le, lf = len(vertices_coords), len(edges_vertices), len(faces_vertices)

    lean = [BASE]
    for i in range(lv):
        lean.append(parse_vertex(i, vertices_coords))
    lean.append("\n")
    for i in range(lf):
        lean.append(parse_face(i, faces_vertices))
    lean.append("\n")
    for i in range(le):
        lean.append(parse_edge(i, edges_vertices, edges_assignment))
    lean.append("\n")
    lean.append(parse_fold(lv, le, lf))
    lean.append(parse_bridge_block())
    return "".join(lean)


def parse_args():
    parser = argparse.ArgumentParser(description="Convert a FOLD JSON file into Lean definitions")
    parser.add_argument("--input", type=Path, default=DEFAULT_INPUT, help="Path to input FOLD JSON")
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT, help="Path to generated Lean file")
    return parser.parse_args()


def main():
    args = parse_args()
    input_path = args.input if args.input.is_absolute() else (ROOT / args.input)
    output_path = args.output if args.output.is_absolute() else (ROOT / args.output)

    with input_path.open("r", encoding="utf-8") as f:
        data = json.load(f)

    lean_code = generate_lean(data)

    output_path.parent.mkdir(parents=True, exist_ok=True)
    with output_path.open("w", encoding="utf-8", newline="\n") as f:
        f.write(lean_code)

    print(f"Generated Lean file: {output_path}")


if __name__ == "__main__":
    main()
