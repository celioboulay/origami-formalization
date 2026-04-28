import Mathlib -- limit to required imports later

set_option linter.style.setOption false
set_option linter.style.multiGoal false
set_option linter.flexible false

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
abbrev Map := Set (Face × Face)

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

/- face_contains f p   is a proof that vertex p is in side face f -/
def face_contains (f : Face) (p : Vertex) : Prop :=
  ((p.x - f.v1.x) * (f.v0.y - f.v1.y) - (f.v0.x - f.v1.x) * (p.y - f.v1.y) ≤ 0 ∧
   (p.x - f.v2.x) * (f.v1.y - f.v2.y) - (f.v1.x - f.v2.x) * (p.y - f.v2.y) ≤ 0 ∧
   (p.x - f.v0.x) * (f.v2.y - f.v0.y) - (f.v2.x - f.v0.x) * (p.y - f.v0.y) ≤ 0) ∨
  (0 ≤ (p.x - f.v1.x) * (f.v0.y - f.v1.y) - (f.v0.x - f.v1.x) * (p.y - f.v1.y) ∧
   0 ≤ (p.x - f.v2.x) * (f.v1.y - f.v2.y) - (f.v1.x - f.v2.x) * (p.y - f.v2.y) ∧
   0 ≤ (p.x - f.v0.x) * (f.v2.y - f.v0.y) - (f.v2.x - f.v0.x) * (p.y - f.v0.y)  )

/- overlap f g   is a proof that f ∩ g ≠ ∅ -/
def overlap (f g : Face) : Prop := -- if overlap, A, B or C must overlap (TODO: prove, if useful)
  (∃ v ∈ f.vertices, face_contains g v) ∨
  (∃ v ∈ g.vertices, face_contains f v)


/- Formalization of a folding Step -/

/- Making sure that moved_F and fixed_F are valid sets that represent F.faces -/
def moved_coherent (F : Fold) (moved_F fixed_F : Set Face) : Prop :=
  moved_F ∪ fixed_F = F.faces ∧ moved_F ∩ fixed_F = ∅

/- map_coherent ensures that every pair in map is indeed made of a face from fixed_F or
  that the corresponding face in g is its reflection by c -/
def map_coherent (c : Crease) (map : Map) (moved_F fixed_F : Set Face) : Prop :=
  ∀ pair ∈ map, pair.1 ∈ fixed_F ∨ (pair.1 ∈ moved_F ∧ folding pair.1 pair.2 c)


/- Step structure includes everything that specify the transition between Fold_i and Fold_i+1 -/
structure Step where
  F : Fold   -- Fold i
  G : Fold   -- Fold i+1
  c : Crease -- the line along which we fold
  map : Map  -- F.faces → G.faces | f ↦ g under the form (f, g) ∈ map
  moved_F : Set Face -- the set of faces of F that move
  fixed_F : Set Face --                      don't move
  moved_coherent : moved_coherent F moved_F fixed_F
  map_coherent : map_coherent c map moved_F fixed_F


/- Correctness of a fold operation -/

/- Ensures that G doesn't "invent" new faces -/
def no_new_face (F G : Fold) (c : Crease) : Prop :=
    ∀ g ∈ G.faces, (g ∈ F.faces) ∨ ( -- every face in G either already existed
      ∃ f ∈ F.faces, folding f g c) -- or is the transformation by c of a previous face

/- Also prove that no face diseaper in the process -/
def no_lost_face (F G : Fold) (c : Crease) : Prop :=
  no_new_face F G c ∧ (F.faces.ncard = G.faces.ncard)


/- Make sure that the previous face orders are compatible with the new ones
  e.g. if face_1 is above face_2 and we fold them over a crease together, then
  face_2 will be above face_1 and their order must be inverted. -/
def previous_orders_ok (moved_F fixed_F : Set Face) (F G : Fold) (map : Map) (c : Crease) : Prop :=
  ∀ fg ∈ F.f_o,
    (fg.1 ∈ fixed_F ∧ fg.2 ∈ fixed_F) -- if none: nothing happens
    ∨ ((fg.1 ∈ moved_F ∧ fg.2 ∈ moved_F ∧ -- both: revert relation
      (∃ g'f' ∈ G.f_o, (fg.1, g'f'.2) ∈ map ∧ (fg.2, g'f'.1) ∈ map)))
    ∨ ((fg.1 ∈ moved_F ∧ fg.2 ∈ fixed_F) ∧ -- can't have f fixed and g moved if f > g so it's fine
      -- ⚠ : we assume full triangulation even on the layers unaffected by the crease
      ∀ f'g' ∈ G.f_o, (f'g'.2 ≠ fg.2 ∨ ¬ folding fg.1 f'g'.1 c))


def new_orders_coherent (map : Map) (G : Fold) (fixed_F : Set Face) : Prop :=
  ∀ pair ∈ map,
    pair.1 = pair.2 ∨ -- face not moved
    (∀ g ∈ fixed_F,
      overlap pair.2 g → (pair.2, g) ∈ G.f_o)

def above_are_moved (F : Fold) (moved_F : Set Face) : Prop :=
  -- may be a better way to frame it but this should work
  ∀ f ∈ moved_F, ∀ f' ∈ F.faces, (f, f') ∈ F.f_o → f' ∈ moved_F


def valid_step (S : Step) : Prop :=
  no_new_face S.F S.G S.c ∧
  no_lost_face S.F S.G S.c ∧
  above_are_moved S.F S.moved_F ∧
  previous_orders_ok S.moved_F S.fixed_F S.F S.G S.map S.c ∧
  new_orders_coherent S.map S.G S.fixed_F
