import json

BASE = """import Origami.FOLD.Properties
import Origami.FOLD.WellFormed
set_option linter.style.emptyLine false\n
"""

with open("data/simple.json") as f:
    d = json.load(f)
    vertices_coords = d['vertices_coords']
    faces_vertices = d['faces_vertices']
    edges_vertices = d['edges_vertices']
    edges_assignment = d['edges_assignment']
    faceOrders = d['faceOrders']

    assert len(edges_assignment)==len(edges_vertices), "pls fix edge size"


lv, le, lf = len(vertices_coords), len(edges_vertices), len(faces_vertices)


def parse_vertex(i):
    return f"def v{i} : Vertex := {{coords := {vertices_coords[i]}}}\n"

def parse_face(i):
    return f"def f{i} : Face := {{verts := {faces_vertices[i]}}}\n"

def parse_edge(i):
    u, v = edges_vertices[i]
    a = edges_assignment[i]
    return f"def e{i} : Edge := {{u := {u}, v := {v}, assignment := EdgeType.{a}}}\n"

# ignored faceOrder for now

def parse_FOLD():
    vertices = "[" + " ".join(f"v{i}," for i in range(lv)) + "]"
    edges = "[" + " ".join(f"e{i}," for i in range(le)) + "]"
    faces = "[" + " ".join(f"f{i}," for i in range(lf)) + "]"

    fold =f"""
def F : Fold :={{
    vertices := {vertices},
    edges    := {edges},
    faces    := {faces}
}}
"""
    return fold

lean = [BASE]
for i in range(lv):
    lean.append(parse_vertex(i))
lean.append("\n")
for i in range(lf):
    lean.append(parse_face(i))
lean.append("\n")
for i in range(le):
    lean.append(parse_edge(i))
lean.append("\n")
lean.append(parse_FOLD())


with open("Origami/FOLD/parsed.lean", 'w') as file:
    file.write("".join(lean))
    file.close()