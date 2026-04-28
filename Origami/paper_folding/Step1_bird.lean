import Origami.paper_folding.GoodProperties

set_option linter.style.setOption false
set_option linter.style.multiGoal false
set_option linter.flexible false


/- Preexisting vertices and faces -/
def A : Vertex := {x := 0,  y := 0}
def B : Vertex := {x := 1, y := 0}
def C : Vertex := {x := 1, y := 1}
def D : Vertex := {x := 0,  y := 1}
def E : Vertex := {x := 1, y := 0}

def f0 : Face := {id := 0, v0 := A, v1 := B, v2 := C}
def f1 : Face := {id := 1, v0 := A, v1 := C, v2 := D}
def f2 : Face := {id := 2, v0 := A, v1 := E, v2 := C} -- new vertex and faces

-- State 1: Paper folded diagonally
def F1 : Fold := {
  faces := {f0, f2}
  f_o := {(f2, f0)}
}

/- We need to prove that this is equivalent to the same fold but after triangulation -/
