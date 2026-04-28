import Origami.paper_folding.BetterProperties
set_option linter.style.setOption false
set_option linter.style.multiGoal false
set_option linter.flexible false

-- code is wrong according to the new definitions but I'll fix later
def A : Vertex := {x := 0,  y := 0}
def B : Vertex := {x := 1, y := 0}
def C : Vertex := {x := 1, y := 1}
def D : Vertex := {x := 0,  y := 1}

-- STEP 1: Paper folded diagonally
def f0 : Face := {v0 := A, v1 := B, v2 := C}
def f2 : Face := {v0 := A, v1 := B, v2 := C} -- new vertex and faces
def F1 : Fold := {
  faces := {f0, f2}
  f_o := [{fa := f2, fb := f0, akb := order.above}]
}

-- triangulation
def T : Vertex := {x := 5, y :=5}
def ft0 : Face := {v0 := A, v1 := B, v2 := T}
def ft1 : Face := {v0 := B, v1 := C, v2 := T}
def ft2 : Face := {v0 := A, v1 := B, v2 := T}
def ft3 : Face := {v0 := B, v1 := C, v2 := T}

-- can make script or automation to show that given points reflect as intended
