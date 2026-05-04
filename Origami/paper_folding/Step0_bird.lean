import Origami.paper_folding.Properties

set_option linter.style.setOption false
set_option linter.style.multiGoal false
set_option linter.flexible false

-- State 0: Flat paper
def A : Vertex := {x := 0,  y := 0}
def B : Vertex := {x := 1, y := 0}
def C : Vertex := {x := 1, y := 1}
def D : Vertex := {x := 0,  y := 1}

def f0 : Face := {id := 0, v0 := A, v1 := B, v2 := C}
def f1 : Face := {id := 1, v0 := A, v1 := C, v2 := D}

def F0 : Fold := {
  faces := {f0, f1}
  f_o := ∅
}

-- State 1: Paper folded diagonally
def E : Vertex := {x := 1, y := 0} -- 1, 0 the reflexion of D by the y=x axis
def f2 : Face := {id := 2, v0 := A, v1 := E, v2 := C}
def F1 : Fold := {
  faces := {f0, f2}
  f_o := {(f2, f0)}
}

-- Step
def c0 : Crease := {a := 1, b := -1, c := 0, nontrivial := by simp}

def m0 (f : Face) : Face :=
  if f = f0 then f0
  else if f = f1 then f2
  else f


def S : Step := {
  F := F0, G := F1, c := c0,
  map := m0,
  map_bijective := by
    unfold F0 F1; simp;
    constructor;
    · use f0; simp;
      unfold m0 f0 f1 f2; simp;
    · use f1; simp;
      unfold m0 f0 f1 f2; simp;

  map_coherent := by
    unfold F0 m0 f0 f1 f2; simp;
    unfold folding reflectVertex A C D E c0; grind;
}

lemma S0a : above_are_moved S.F S.map := by
  unfold above_are_moved S F0 F1; simp

lemma S0b : previous_orders_ok S.F S.G S.map := by
  unfold previous_orders_ok S F0 F1; simp;

lemma S0c : new_orders_coherent S.map S.F S.G := by
  unfold new_orders_coherent S F0 F1 m0 f0 f1 f2; simp;

theorem step0_is_valid : valid_step S := by
  unfold valid_step; simp[S0a, S0b, S0c]
