import Origami.paper_folding.Properties

set_option linter.style.setOption false
set_option linter.style.multiGoal false
set_option linter.flexible false


/- Vertices and Faces
I will upload reference annotated paper
or maybe I won't -/
def A : Vertex := {x := 0,   y := 0}
def B : Vertex := {x := 1,   y := 0}
def C : Vertex := {x := 1,   y := 1}
def E : Vertex := {x := 1,   y := 3/4}
def F : Vertex := {x := 1/4, y := 0}
def G : Vertex := {x := 1/4, y := -1/4}
def H : Vertex := {x := 5/4, y := 3/4}

def f0 : Face := {id := 0, v0 := F, v1 := B, v2 := E}
def f1 : Face := {id := 1, v0 := F, v1 := E, v2 := A}
def f2 : Face := {id := 2, v0 := A, v1 := E, v2 := C}
def f3 : Face := {id := 3, v0 := F, v1 := B, v2 := E}
def f4 : Face := {id := 4, v0 := F, v1 := E, v2 := A}
def f5 : Face := {id := 5, v0 := A, v1 := E, v2 := C}
def f6 : Face := {id := 6, v0 := G, v1 := E, v2 := F}
def f7 : Face := {id := 7, v0 := G, v1 := H, v2 := E}
def f8 : Face := {id := 8, v0 := G, v1 := H, v2 := E}
def f9 : Face := {id := 9, v0 := G, v1 := E, v2 := F}

def c1 : Crease := {a := 1, b := -1, c := -1/4, nontrivial := by simp}


-- State 1: Paper folded diagonally
-- this Fold is equivalent to the F1 of step 0 (yet to be proven but trust)
def F1 : Fold := {
  faces := {f0, f1, f2, f3, f4, f5}
  f_o := {(f3, f0), (f4, f1), (f5, f2)}
}

def F2 : Fold := {
  faces := {f0, f3, f6, f7, f8, f9}
  f_o := {(f3, f0), (f7, f8), (f6, f9),
          (f6, f0), (f7, f0), (f8, f0), (f9, f0),
          (f6, f3), (f7, f3), (f8, f3), (f9, f3)}
}


def m1 (f : Face) : Face :=
  if f = f0 then f0
  else if f = f3 then f3
  else if f = f1 then f6
  else if f = f2 then f7
  else if f = f4 then f9
  else if f = f5 then f8
  else f


def S : Step := {
  F := F1, G := F2, c := c1,
  map := m1,
  map_bijective := by sorry
  map_coherent := by sorry
}
