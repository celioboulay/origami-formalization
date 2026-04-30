import Origami.paper_folding.GoodProperties

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

#eval (reflectVertex c1 C)

-- State 1: Paper folded diagonally
-- this Fold is equivalent to the F1 of step 0 (yet to be proven but trust)
def F1 : Fold := {
  faces := {f0, f1, f2, f3, f4, f5}
  f_o := {(f3, f0), (f4, f1), (f5, f2)}
}

def F2 : Fold := {
  faces := {f0, f3, f6, f7, f8, f9}
  f_o := {(f3, f0), (f7, f8), (f6, f9), -- ⚠ YO WHY IS F4 IN THERE?????
          (f6, f0), (f7, f0), (f8, f0), (f9, f0),
          (f6, f3), (f7, f3), (f8, f3), (f9, f3)}
}

lemma f1c1f6 : folding f1 f6 c1 := by
  unfold folding reflectVertices reflectVertex;
  simp [Face.vertices];
  unfold f1 f6 A E F G c1;
  ext x; constructor;
  simp; grind; simp; grind;

lemma f2c1f7 : folding f2 f7 c1 := by
  unfold folding reflectVertices reflectVertex;
  simp [Face.vertices]; unfold f2 f7 A H G E C c1;
  ext x; constructor;
  simp; grind; simp; grind;

lemma f5c1f8 : folding f5 f8 c1 := by
  unfold folding reflectVertices reflectVertex;
  simp [Face.vertices]; unfold f5 f8 G H E C A c1;
  ext x; constructor;
  simp; grind; simp; grind;

lemma f4c1f9 : folding f4 f9 c1 := by
  unfold folding reflectVertices reflectVertex;
  simp [Face.vertices]; unfold f4 f9 G E F A c1;
  ext x; constructor;
  simp; grind; simp; grind;


def S1 : Step := {
  F := F1, G := F2, c := c1,
  map := {(f0, f0), (f3, f3), (f1, f6), (f2, f7), (f4, f9), (f5, f8)},
  moved_F := {f1, f2, f4, f5}
  fixed_F := {f0, f3},
  moved_coherent := by
    unfold moved_coherent F1; simp;
    unfold f0 f1 f2 f3 f4 f5; grind;
  map_coherent := by
    unfold map_coherent;
    simp [f1c1f6, f2c1f7, f5c1f8, f4c1f9];
}

/- Proof of the example -/
lemma S1a : no_new_face S1.G S1.moved_F S1.fixed_F S1.c := by
  unfold no_new_face S1; simp; unfold F2;
  simp [f1c1f6, f2c1f7, f5c1f8, f4c1f9];

lemma S1b : no_lost_face S1.F S1.G S1.moved_F S1.fixed_F S1.c := by
  unfold no_lost_face;
  simp [S1a];
  unfold S1 F1 F2 f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 A B C E F G;
  simp;

lemma S1c : above_are_moved S1.F S1.moved_F := by
  unfold above_are_moved;
  unfold S1 c1 F1 F2 f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 A B C E F G;
  simp;

lemma S1d : previous_orders_ok S1.moved_F S1.fixed_F S1.F S1.G S1.map S1.c := by
  unfold previous_orders_ok; simp;
  unfold S1 F1; simp;
  intro a b h;
  unfold F2; simp;
  rcases h with h1 | h2 | h3
  · left; simp [h1]
  · simp [h2]; right;
    unfold f0 f1 f2 f3 f4 f5 f6 f7 f8 f9; simp;
  · simp [h3]; unfold f0 f1 f2 f3 f4 f5 f6 f7 f8 f9; simp;

lemma S1e : new_orders_coherent S1.map S1.G S1.fixed_F := by
  unfold new_orders_coherent S1 F1 F2; simp;


theorem S0valid : valid_step S1 := by
  unfold valid_step
  simp [S1a, S1b, S1c, S1d, S1e]

/- We need to prove that this is equivalent to the same fold but after triangulation -/
