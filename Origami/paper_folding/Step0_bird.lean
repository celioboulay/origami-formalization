import Origami.paper_folding.GoodProperties

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
def f2 : Face := {id := 2, v0 := A, v1 := E, v2 := C} -- new vertex and faces
def F1 : Fold := {
  faces := {f0, f2}
  f_o := {(f2, f0)}
}

def c0 : Crease := {a := 1, b := -1, c := 0, nontrivial := by simp}

lemma f1c0f2 : folding f1 f2 c0 := by
  unfold folding reflectVertices reflectVertex;
  simp [Face.vertices];
  unfold f1 f2 A C D E c0;
  ext x; constructor;
  simp; grind; simp; grind;


-- the Step
def S0 : Step := {
  F := F0, G := F1, c := c0,
  map := {(f0, f0), (f1, f2)},
  moved_F := {f1},
  fixed_F := {f0},
  moved_coherent := by
    unfold moved_coherent f1 f0; simp;
    unfold F0 f0 f1; simp;

  map_coherent := by -- prove as a lemma
    unfold map_coherent;
    simp; right; simp [f1c0f2];
}

/- Proof of the example -/
lemma A0A : reflectVertex c0 A = A := by
  unfold A c0 reflectVertex; ring_nf;
lemma D0E : reflectVertex c0 D = E := by
  unfold D c0 reflectVertex E; ring_nf;
lemma C0C : reflectVertex c0 C = C := by
  unfold C c0 reflectVertex; ring_nf;

lemma S0a : no_new_face S0.F S0.G S0.c := by
  unfold no_new_face S0
  intro g hg
  simp; simp at hg;
  cases hg with
  | inl h1 =>
    unfold F0; grind;
  | inr h2 =>
    unfold F0; simp; right; right;
    unfold folding reflectVertices;
    simp [Face.vertices]
    ext x; constructor; intro hx;
    rcases hx with rfl | rfl | rfl
    · simp_all; unfold f1 f2; simp; simp [A0A]
    · simp_all; unfold f1 f2; simp; simp [D0E]
    · simp_all; unfold f1 f2; simp; simp [C0C]
    intro hx; unfold f1 at hx; simp at hx;
    simp;
    rcases hx with ha | hb | hc
    · rw [A0A] at ha; simp at h2; rw [h2]; unfold f2; simp_all;
    · rw [C0C] at hb; simp at h2; rw [h2]; unfold f2; simp_all;
    · rw [D0E] at hc; simp at h2; rw [h2]; unfold f2; simp_all;


lemma S0b : no_lost_face S0.F S0.G S0.c := by
  unfold no_lost_face
  simp [S0a];
  unfold S0 F0 F1; simp;
  have h1 : f0 ≠ f1 := by unfold f0 f1 A B C D; grind;
  have h2 : f0 ≠ f2 := by unfold f0 f2 A B C E; grind; -- le pb des points
  simp [h1, h2]


lemma S0c : above_are_moved S0.F S0.moved_F := by
  unfold above_are_moved S0 c0 f0 f1 f2 A B C D E;
  simp_all; unfold F0 f0 f1 A B C D;
  simp; -- need a better way to write this, this was random


lemma S0d : previous_orders_ok S0.moved_F S0.fixed_F S0.F S0.G S0.map S0.c := by
  unfold previous_orders_ok S0; simp;
  intro f f' h;
  unfold F0 at h; trivial; -- F0.f_o = ∅ so trivial

lemma S0e : new_orders_coherent S0.map S0.G S0.fixed_F := by
  unfold new_orders_coherent S0 F0 F1; simp;


theorem S0valid :valid_step S0 := by
  unfold valid_step
  simp [S0a, S0b, S0c, S0d, S0e]

/- Also need to prove that the parcelation is ↔ to the i-1 + crease -/
