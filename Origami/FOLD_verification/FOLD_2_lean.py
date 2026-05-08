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

def get_label(i): # for larger crease patterns with AA AB and so on (Excel ouuuu)
    res = ""
    while i >= 0:
        res = chr(65 + (i % 26)) + res
        i = (i // 26) - 1
    return res

def build_lean_from_fold(fold_path: Path, output_path: Path) -> None:
    edges = parse_fold_file(str(fold_path))['edges']
    vertices = parse_fold_file(str(fold_path))['vertices']
    assignments = parse_fold_file(str(fold_path))['assignments']

    id_point_2_letter = {}
    for i, p in enumerate(vertices):
        id_point_2_letter[i] = get_label(i) 

    rays = []
    for i, edge in enumerate(edges):
        if assignments[i] in ['V', 'M']:
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
set_option linter.style.emptyLine false
set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option linter.flexible false\n
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

    P = "def P : CreasePattern := {\n" + "  γ := {" + ", ".join(γ) + "},\n" +\
          "  V := {" + ", ".join(V) + "},\n" + "  E := {" + ", ".join(E) + "}\n}"

    if not γ: # if γ = ∅ it is trivial so the proof is simpler
        proof = "theorem P_M : Maekawa_condition P := by\n  unfold Maekawa_condition P; simp;\n"
        lean = IMPORTS + "\n".join(points_lines) + "\n\n" + "\n".join(rays_lines) + "\n" + P + "\n\n" + proof
        output_path.parent.mkdir(parents=True, exist_ok=True)
        with output_path.open("w", encoding="utf-8") as f:
            f.write(lean)
        return

    if not rays: #TODO
        note = "-- Maekawa condition skipped\n"
        lean = IMPORTS + "\n".join(points_lines) + "\n\n" + "\n".join(rays_lines) + "\n\n" + P + "\n\n" + note
        output_path.parent.mkdir(parents=True, exist_ok=True)
        with output_path.open("w", encoding="utf-8") as f:
            f.write(lean)
        return
    
    if len(γ) > 0:
        Maekawa_c = f"""theorem P_M : Maekawa_condition P := by
  unfold Maekawa_condition;
  intro v hv;
  unfold P at hv; simp only at hv;\n""" # statement and first line of the proof before entering rcases
        
        rc = ["rfl"] * len(γ) # building rcases size based on the number of vertices to check
        sep_vert = " | " # otherwise f string is not happy
        sep_comma = ", "
        rcases = f"  rcases hv with ({sep_vert.join(rc)})\n"


        def sets(i):
            raysM, raysV = [], []
            for r in rays:
                if γ[i] in (r[0], r[1]):
                    if r[2] == 'M':
                        raysM.append(f"{r[0]}{r[1]}")
                    else:
                        raysV.append(f"{r[0]}{r[1]}")

            setM = f"{{{sep_comma.join(raysM)}}}" if raysM else "∅"
            setV = f"{{{sep_comma.join(raysV)}}}" if raysV else "∅"

            return setM, setV


        # helper for the next step, we can basically simp [everything] and it won't crash (unlike unfold which requires args to be in the goal)
        simpAll = f"simp [M, V, P, {sep_comma.join(E)}, {sep_comma.join(V)}, {sep_comma.join(γ)}];"

        def proof_case(i): # solving subcase where v = γ[i]
            setM, setV = sets(i)
            proof = f"""  · -- Case v = {γ[i]}
    intro M n_M V n_V;
    have hM : M = {setM} := by
      ext e; {simpAll} grind;
    have hV : V = {setV} := by
      ext e; {simpAll} grind;
    unfold n_M n_V; simp [hM, hV]; {simpAll} norm_num;
    """
            return proof
        
        rcasesproof = "\n".join([proof_case(i) for i in range(len(γ))])


        # Assembling the proof
        lean = IMPORTS + "\n".join(points_lines) + "\n\n" + "\n".join(rays_lines) + \
            "\n\n" + P + "\n\n" + Maekawa_c + rcases + rcasesproof + '\n'

        # Saving the proof as a .lean file
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
