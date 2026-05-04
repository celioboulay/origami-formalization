import Mathlib -- limit to required imports later

/- Cleaning GoodProperties.lean
Will simplfy proofs and make sure physics is satisfied
you can ignore this file until this comment is not removed -/

set_option linter.style.setOption false
set_option linter.style.multiGoal false
set_option linter.flexible false

/- Structures -/
structure Vertex where -- using ℚ instead of ℝ to make things computable
  x : ℚ
  y : ℚ
deriving instance BEq, ReflBEq, LawfulBEq, DecidableEq for Vertex

structure Face where -- triangle | vertices counter-clockwise
  id : ℕ
  v0 : Vertex
  v1 : Vertex
  v2 : Vertex
  nontrivial : v0 ≠ v1 ∧ v0 ≠ v2 ∧ v1 ≠ v2
deriving instance BEq, DecidableEq for Face

abbrev FacePair := Face × Face -- maybe for face_orders?


structure Fold where
  faces : Set Face
  f_o : Set FacePair -- or define new order relation

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


def folding (f g : Face) (c : Crease) : Prop :=
  reflectVertex c f.v0 = g.v0 ∧
  reflectVertex c f.v1 = g.v2 ∧
  reflectVertex c f.v2 = g.v1

/- face_contains f p   is a proof that vertex p is in side face f -/
def face_contains (f : Face) (p : Vertex) : Prop :=
  ((p.x - f.v1.x) * (f.v0.y - f.v1.y) - (f.v0.x - f.v1.x) * (p.y - f.v1.y) ≤ 0 ∧
   (p.x - f.v2.x) * (f.v1.y - f.v2.y) - (f.v1.x - f.v2.x) * (p.y - f.v2.y) ≤ 0 ∧
   (p.x - f.v0.x) * (f.v2.y - f.v0.y) - (f.v2.x - f.v0.x) * (p.y - f.v0.y) ≤ 0) ∨
  (0 ≤ (p.x - f.v1.x) * (f.v0.y - f.v1.y) - (f.v0.x - f.v1.x) * (p.y - f.v1.y) ∧
   0 ≤ (p.x - f.v2.x) * (f.v1.y - f.v2.y) - (f.v1.x - f.v2.x) * (p.y - f.v2.y) ∧
   0 ≤ (p.x - f.v0.x) * (f.v2.y - f.v0.y) - (f.v2.x - f.v0.x) * (p.y - f.v0.y)  )

/- overlap f g   is a proof that f ∩ g ≠ ∅ -/
def overlap (f g : Face) : Prop := -- if overlap, A, B or C must overlap
  (∃ v ∈ [f.v0, f.v1, f.v2], face_contains g v) ∨
  (∃ v ∈ [g.v0, g.v1, g.v2], face_contains f v)


/- Formalization of a folding Step -/

/- Step structure includes everything that specify the transition between Fold_i and Fold_i+1 -/
structure Step where
  F : Fold   -- Fold i
  G : Fold   -- Fold i+1
  c : Crease -- the line along which we fold
  map : Face → Face  -- F.faces → G.faces | f ↦ g under the form (f, g) ∈ map
  map_bijective : ∀ g ∈ G.faces, ∃! f ∈ F.faces, map f = g -- Function.Bijective was annoying


/- Correctness of a fold operation -/

def no_new_face (F G : Fold) (map : Face → Face) : Prop :=
    ∀ g ∈ G.faces, ∃ f ∈ F.faces, map f = g

/- Also prove that no face diseaper in the process -/
def no_lost_face (F G : Fold) : Prop := F.faces.ncard = G.faces.ncard


/- Make sure that the previous face orders are compatible with the new ones
  e.g. if face_1 is above face_2 and we fold them over a crease together, then
  face_2 will be above face_1 and their order must be inverted. -/
def previous_orders_ok (F G : Fold) (map : Face → Face) (c : Crease) : Prop :=
  ∀ fg ∈ F.f_o,
    (map fg.1 = fg.1 ∧ map fg.2 = fg.2) -- if none: nothing happens
    ∨ ((map fg.1 ≠ fg.1 ∧ map fg.2 ≠ fg.2 ∧ -- both: revert relation
      (∃ g'f' ∈ G.f_o, map fg.1 = g'f'.2 ∧ map fg.2 = g'f'.1)))
    ∨ ((map fg.1 ≠ fg.1 ∧ map fg.2 = fg.2) ∧ -- can't have f fixed and g moved if f > g so it's fine
      ∀ f'g' ∈ G.f_o, (f'g'.2 ≠ fg.2 ∨ ¬ folding fg.1 f'g'.1 c))


def new_orders_coherent (map : Face → Face) (F G : Fold) : Prop :=
  ∀ f ∈ F.faces,
    map f = f ∨ -- face not moved
    (∀ g ∈ F.faces, (map g = g ∧ -- fixed_F
      overlap (map f) g) → (map f, g) ∈ G.f_o)

def above_are_moved (F : Fold) (map : Face → Face) : Prop :=
  ∀ f ∈ F.faces, ∀ f' ∈ F.faces,
    (f, f') ∈ F.f_o → map f ≠ f → map f' ≠ f'  -- f' is also moved
    -- moved faces = {f ∈ F.faces s.t. map f ≠ f}




def valid_step (S : Step) : Prop :=
  no_new_face S.F S.G S.map ∧
  no_lost_face S.F S.G ∧
  above_are_moved S.F S.map ∧
  previous_orders_ok S.F S.G S.map S.c ∧
  new_orders_coherent S.map S.F S.G
