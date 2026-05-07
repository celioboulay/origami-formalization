import os
import json

ROOT_DIR = os.path.dirname(os.path.abspath(__file__))

def parse_fold_file(file_path):
    with open(file_path, 'r') as f:
        data = json.load(f)

    return {
        'vertices': data.get('vertices_coords', []),
        'edges': data.get('edges_vertices', []),
        'assignments': data.get('edges_assignment', [])
    }

fold_path = f"{ROOT_DIR}/../../data/crease_pattern_1.json"
edges = parse_fold_file(fold_path)['edges']
vertices = parse_fold_file(fold_path)['vertices']
assignments = parse_fold_file(fold_path)['assignments']

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

lean = IMPORTS + "\n".join(points_lines) + "\n\n" + "\n".join(rays_lines) + "\n"


with open(f"{ROOT_DIR}/parsed.lean", "w") as f:
  f.write(lean)