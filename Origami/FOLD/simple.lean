import Origami.FOLD.Properties
import Origami.FOLD.WellFormed
set_option linter.style.emptyLine false

def v0 : Vertex := {coords := [0, 1, 0]}
def v1 : Vertex := {coords := [0, 0, 1]}
def v2 : Vertex := {coords := [0,-1, 0]}
def v3 : Vertex := {coords := [1, 0, 0]}
def v4 : Vertex := {coords := [0, 0,-1]}
def v5 : Vertex := {coords := [0, 0,-1]}


def f0 : Face := {verts := [0,1,2]}
def f1 : Face := {verts := [0,2,3]}
def f2 : Face := {verts := [0,4,1]}
def f3 : Face := {verts := [1,5,2]}

def e0 : Edge := {u := 0, v := 2, assignment := EdgeType.V}
def e1 : Edge := {u := 0, v := 1, assignment := EdgeType.M}
def e2 : Edge := {u := 1, v := 2, assignment := EdgeType.M}
def e3 : Edge := {u := 2, v := 3, assignment := EdgeType.B}
def e4 : Edge := {u := 0, v := 3, assignment := EdgeType.B}
def e5 : Edge := {u := 1, v := 4, assignment := EdgeType.B}
def e6 : Edge := {u := 1, v := 5, assignment := EdgeType.B}
def e7 : Edge := {u := 0, v := 4, assignment := EdgeType.B}
def e8 : Edge := {u := 2, v := 5, assignment := EdgeType.B}

def F : Fold := {
  vertices := [v0, v1, v2, v3, v4, v5],
  edges    := [e0, e1, e2, e3, e4, e5, e6, e7, e8],
  faces    := [f0, f1, f2, f3]
}


theorem wellFormed_F : WellFormed F := by
  unfold F

  have ewi : ∀ e  ∈ F.edges, EdgeWellIndexed F e := by
    intro e he
    fin_cases he <;> trivial

  have fwi : ∀ f ∈ F.faces, FaceWellIndexed F f := by
    intro x hx y hy
    fin_cases hx <;> fin_cases hy <;> trivial

  have h2 : SameDimension F := by
    intro x hx y hy
    fin_cases hx <;> fin_cases hy <;> trivial

  have h3 : FacesHaveSizeGE3 F := by
    intro x hx
    fin_cases hx <;> trivial

  have h4 : NoDegenerateEdges F := by
    intro x hx
    fin_cases hx <;> trivial

  have h5 : FacesNoDuplicates F := by
    intro x hx
    fin_cases hx <;> trivial

  trivial
