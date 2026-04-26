import Mathlib

set_option linter.style.setOption false
set_option linter.style.multiGoal false
set_option linter.flexible false


structure Vertex where
  x : ℚ
  y : ℚ

structure Face where -- triangulate
  v0 : Vertex
  v1 : Vertex
  v2 : Vertex

inductive order where
  | above
  | under
  | NA

structure FaceOrder where
  fa : Face
  fb : Face
  akb : order -- fa is "k" fb

structure Fold where
  faces : Set Face
  f_o : List FaceOrder


-- crease and Fold
-- only the faces that moved need to be checked
structure Crease where
  a : ℚ
  b : ℚ
  c : ℚ
  nontrivial : a ≠ 0 ∨ b ≠ 0



def reflectVertex (c : Crease) (p : Vertex) : Vertex :=
  let d := (c.a * p.x + c.b * p.y + c.c) / (c.a^2 + c.b^2)
  { x := p.x - 2 * c.a * d
    y := p.y - 2 * c.b * d }

def Face.vertices (f : Face) : Set Vertex :=
  {f.v0, f.v1, f.v2}

def reflectVertices (c : Crease) (f : Face) : Set Vertex :=
  reflectVertex c '' f.vertices

def folding (f g : Face) (c : Crease) : Prop :=
  g.vertices = reflectVertices c f

def reachable (F G : Fold) : Prop :=
  ∃ (c : Crease),
    ∀ g ∈ G.faces, (g ∈ F.faces) ∨ (
      ∃ f ∈ F.faces, folding f g c)


-- Flat paper: step 0
def A : Vertex := {x := 0,  y := 0}
def B : Vertex := {x := 10, y := 0}
def C : Vertex := {x := 10, y := 10}
def D : Vertex := {x := 0,  y := 10}

def f0 : Face := {v0 := A, v1 := B, v2 := C}
def f1 : Face := {v0 := A, v1 := C, v2 := D}

def F0 : Fold := {
  faces := {f0, f1}
  f_o := []
}

-- Paper folded diagonally : step 0
def E : Vertex := {x := 10, y := 0} -- 10, 0 the reflexion of D by the y=x axis
def f2 : Face := {v0 := A, v1 := E, v2 := C} -- new vertex and faces
def F1 : Fold := {
  faces := {f0, f2}
  f_o := [{fa := f0, fb := f2, akb := order.above}]
}

def c0 : Crease := {a := 1, b := -1, c := 0, nontrivial := by simp}




-- Vertex_i | step_i | Vertex_i+1
lemma A0A : reflectVertex c0 A = A := by
  unfold A c0 reflectVertex; ring_nf;
lemma D0E : reflectVertex c0 D = E := by
  unfold D c0 reflectVertex E; ring_nf;
lemma C0C : reflectVertex c0 C = C := by
  unfold C c0 reflectVertex; ring_nf;

-- proof that Fold0 to Fold1 is possible:
theorem step0 : reachable F0 F1 := by
  use c0
  unfold F0 F1 f0 f1 f2
  intro g hg
  simp; simp at hg
  cases hg with
  | inl h1 =>
    left; left; exact h1;
  | inr h2 =>
    right; right;
    subst h2
    unfold folding reflectVertices
    simp [Face.vertices]
    ext x
    constructor
    -- →
    intro hx
    rcases hx with rfl | rfl | rfl
    · simp [Set.mem_image]; simp [A0A];
    · simp [Set.mem_image]; simp[D0E];
    · simp [Set.mem_image]; simp[C0C];
    -- ←
    intro hx
    simp at hx; simp
    rcases hx with rfl | rfl | rfl
    simp [A0A]; simp[C0C]; simp[D0E];
