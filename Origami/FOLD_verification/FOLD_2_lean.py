import argparse
import json
import os
from pathlib import Path

ROOT_DIR = Path(__file__).resolve().parent

def parse_fold_file(file_path):
    with open(file_path, 'r') as f:
        data = json.load(f)

    return {
        'vertices': data.get('vertices_coords', []),
        'edges': data.get('edges_vertices', []),
        'assignments': data.get('edges_assignment', [])
    }

def build_lean_from_fold(fold_path: Path, output_path: Path) -> None:
    edges = parse_fold_file(str(fold_path))['edges']
    vertices = parse_fold_file(str(fold_path))['vertices']
    assignments = parse_fold_file(str(fold_path))['assignments']

    id_point_2_letter = {}
    for i, p in enumerate(vertices):
        id_point_2_letter[i] = chr(ord('A') + i) # fix for larger crease patterns with AA AB and so on

    rays = []
    for i, edge in enumerate(edges):
        if assignments[i] not in ['V', 'M']:
            continue
        else:
            n_u, n_v = edge
            u, v = id_point_2_letter[n_u], id_point_2_letter[n_v]
            rays.append([u, v, assignments[i]])

    points_lines = [
        f"def {id_point_2_letter[i]} : Point := ⟨{p[0]}, {p[1]}⟩"
        for i, p in enumerate(vertices)]

    rays_lines = [
        f"def {r[0]}{r[1]} : Ray := ⟨{r[0]}, {r[1]}, Label.{r[2]}⟩"
        for r in rays]

    IMPORTS = """import Origami.FOLD_verification.crease_pattern_verif
set_option linter.style.emptyLine false\n
"""

    γ, V, E = [], [], rays
    for i, p in enumerate(vertices):
        if (p[0]==0 or p[1]==0 or p[0]==1 or p[1]==1):
            V.append(id_point_2_letter[i])
        else: # if inside of the square it is a so called Vertex
            γ.append(id_point_2_letter[i])

    γ = [f"{Vertex}" for Vertex in γ]
    V = [f"{Point}" for Point in V]
    E = [f"{Edge[0]}{Edge[1]}" for Edge in E]

    P = "def P : CreasePattern := {\n" + "  γ := {" + ", ".join(γ) + "},\n" + "  V := {" + ", ".join(V) + "},\n" + "  E := {" + ", ".join(E) + "}\n}"

    n_M, n_V = assignments.count('M'), assignments.count('V')

    if not γ:
        lean = IMPORTS + "\n".join(points_lines) + "\n\n" + "\n".join(rays_lines) + "\n\n" + P + "\n\n" + "-- No interior vertices; Maekawa condition skipped.\n"
        output_path.parent.mkdir(parents=True, exist_ok=True)
        with output_path.open("w", encoding="utf-8") as f:
            f.write(lean)
        return

    Maekawa_c = f"""theorem P_M : Maekawa_condition P := by
  unfold Maekawa_condition;
  intro v hv M n_M V n_V
  replace hv : v = {γ[0]} := hv; subst hv\n
  """

    raysM, raysV = [], []
    for r in rays:
        if r[2] == 'M':
            raysM.append(f"{r[0]}{r[1]}")
        else:
            raysV.append(f"{r[0]}{r[1]}")

    setM = ", ".join(raysM) if raysM else "∅"
    setV = ", ".join(raysV) if raysV else "∅"

    hM = f"""have hM : M = {{{setM}}} := by
    ext e; unfold M P {" ".join(E)}; simp; grind;\n\n
"""

    hV = f"""  have hV : V = {{{setV}}} := by
    ext e; unfold V P {" ".join(E)}; simp; grind;\n\n
"""

    unfoldhnM = " ".join(raysM)
    unfoldhnV = " ".join(raysV)
    verticesM, verticesV = set(), set()
    for r in raysM:
        verticesM.add(r[0])
        verticesM.add(r[1])
    for r in raysV:
        verticesV.add(r[0])
        verticesV.add(r[1])

    hnMV = f"""  have hnM : n_M = {n_M} := by
    unfold n_M; rw [hM];
    unfold {unfoldhnM} {" ".join(verticesM)}; norm_num;

  have hnV : n_V = {n_V} := by
    unfold n_V; rw [hV];
    unfold {unfoldhnV} {" ".join(verticesV)}; norm_num;\n\n"""

    end = "  simp [hnM, hnV];\n"

    lean = IMPORTS + "\n".join(points_lines) + "\n\n" + "\n".join(rays_lines) + \
        "\n\n" + P + "\n\n" + Maekawa_c + hM + hV + hnMV + end

    output_path.parent.mkdir(parents=True, exist_ok=True)
    with output_path.open("w", encoding="utf-8") as f:
        f.write(lean)


def main() -> int:
    parser = argparse.ArgumentParser(description="Convert FOLD to Lean")
    parser.add_argument(
        "--input",
        default=str(ROOT_DIR / ".." / ".." / "data" / "crease_pattern_2.json"),
        help="Path to the FOLD JSON file",
    )
    parser.add_argument(
        "--output",
        default=str(ROOT_DIR / "parsed.lean"),
        help="Path for the generated Lean file",
    )
    args = parser.parse_args()

    fold_path = Path(args.input)
    output_path = Path(args.output)
    build_lean_from_fold(fold_path, output_path)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

