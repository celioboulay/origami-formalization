import Mathlib -- limit to required imports later

set_option linter.style.setOption false
set_option linter.style.multiGoal false
set_option linter.flexible false

def TODO : Prop := 1 = 1 -- temporary placeholder

/- Structures -/
structure Vertex where -- using ℚ instead of ℝ to make things computable
  x : ℚ
  y : ℚ

structure Face where -- triangle | vertices counter-clockwise
  id : ℕ
  v0 : Vertex
  v1 : Vertex
  v2 : Vertex


abbrev FacePair := Face × Face

abbrev Map := Set (Face × Face) -- ∀ f ∈ F, ∃! g ∈ G s.t. (f, g) ∈ map. also |F| = |G|

structure Fold where
  faces : Set Face
  f_o : Set FacePair

structure Crease where -- line
  a : ℚ
  b : ℚ
  c : ℚ
  nontrivial : a ≠ 0 ∨ b ≠ 0


/- Reflections and folding definitions -/
def reflectVertex (c : Crease) (p : Vertex) : Vertex :=
  let d := (c.a * p.x + c.b * p.y + c.c) / (c.a^2 + c.b^2)
  { x := p.x - 2 * c.a * d
    y := p.y - 2 * c.b * d }

def Face.vertices (f : Face) : Set Vertex :=
  {f.v0, f.v1, f.v2}

def reflectVertices (c : Crease) (f : Face) : Set Vertex :=
  reflectVertex c '' f.vertices -- the image of f.vertices by crease c

def folding (f g : Face) (c : Crease) : Prop :=
  g.vertices = reflectVertices c f


def side (c : Crease) (p : Vertex) : ℚ := c.a * p.x + c.b * p.y + c.c

/- Formalization of a folding Step -/
def moved_coherent (F : Fold) (c : Crease) (moved_F fixed_F : Set Face) : Prop := -- needed below
-- this assumes discrete folds and not weird foldings like first few steps of the crane
  moved_F ∪ fixed_F = F.faces ∧
  moved_F ∩ fixed_F = ∅ ∧
 ( ∀ moved ∈ moved_F, ∀ fixed ∈ fixed_F, -- c split the vertices, one side for each set
   ∀ pm ∈ moved.vertices, ∀ pf ∈ fixed.vertices, -- may be annoying to prove if not auto
   side c pm * side c pf <= 0 )


def map_coherent (c : Crease) (map : Map) (fixed_F : Set Face) : Prop :=
  ∀ pair ∈ map, pair.1 ∈ fixed_F ∨ folding pair.1 pair.2 c
-- we can use map to simplify things in no_new_face


structure Step where -- we check that this step is valid after
  F : Fold -- initial Fold (i)
  G : Fold -- Fold at time i+1
  c : Crease -- the line along which we crease
  map : Map
  moved_F : Set Face -- the set of faces of F that move
  fixed_F : Set Face                      -- don't move
  moved_coherent : moved_coherent F c moved_F fixed_F
  map_coherent : map_coherent c map fixed_F


/- Correctness of a fold operation -/
def no_new_face (F G : Fold) (c : Crease) : Prop :=
    ∀ g ∈ G.faces, (g ∈ F.faces) ∨ ( -- either already existed
      ∃ f ∈ F.faces, folding f g c) -- or the transformation of a previous face by c

def no_lost_face (F G : Fold) (c : Crease) : Prop :=
  no_new_face F G c ∧ (F.faces.ncard = G.faces.ncard)

def face_order_stay_coherent (map : Map) (moved_F fixed_F : Set Face) (F G : Fold) : Prop :=
  -- this ensures the preexisting orders are conserved
  ∀ fg ∈ F.f_o,
   -- if both are moved, the relation of the images in G is reversed
    (fg.1 ∈ fixed_F ∧ fg.2 ∈ fixed_F) -- if none: nothing happens
    ∨ (fg.1 ∈ moved_F ∧ fg.2 ∈ moved_F ∧ -- both: revert relation
      ((fg ∈ F.f_o ∧ fg.swap ∈ G.f_o) ∨ (fg ∈ F.f_o ∧ fg.swap ∈ G.f_o))) -- ⚠ may not be in f_o
    ∨ (fg.1 ∈ moved_F ∧ fg.2 ∈ fixed_F ∧ TODO) -- if only one: break relation
   -- *find a way to get the moved face and not just vertices → moved / fixed*


def above_are_moved (F : Fold) (moved_F : Set Face) : Prop :=
  -- may be a better way to frame it but this should work
  ∀ f ∈ moved_F, ∀ f' ∈ F.faces, (f, f') ∈ F.f_o → f' ∈ moved_F


def valid_step (S : Step) : Prop :=
  no_new_face S.F S.G S.c ∧
  no_lost_face S.F S.G S.c ∧
  above_are_moved S.F S.moved_F ∧
  face_order_stay_coherent S.map S.moved_F S.fixed_F S.F S.G



/- Example -/ -- probably move into an other file soon
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
  f_o := {(f0, f1)}
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
    simp [Face.vertices];
    unfold A B C D side c0; grind;

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


lemma S0d : face_order_stay_coherent S0.map S0.moved_F S0.fixed_F S0.F S0.G := by sorry


theorem S0valid :valid_step S0 := by
  unfold valid_step
  simp [S0a, S0b, S0c, S0d]

-- pour montre dans lautre sens que pas de face est supprimme juste check si le cardinal est le meme


/- Also need to prove that the parcelation is ↔ to the i-1 + crease -/
