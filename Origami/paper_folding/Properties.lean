import Origami.paper_folding.Structures

/- Reflections and folding definitions -/
def reflectVertex (c : Crease) (p : Vertex) : Vertex :=
  let d := (c.a * p.x + c.b * p.y + c.c) / (c.a^2 + c.b^2)
  { x := p.x - 2 * c.a * d
    y := p.y - 2 * c.b * d }


def folding (f g : Face) (c : Crease) : Prop :=
  reflectVertex c f.v0 = g.v0 ∧
  reflectVertex c f.v1 = g.v2 ∧
  reflectVertex c f.v2 = g.v1

-- face_contains f p   is a proof that vertex p is in side face f
def face_contains (f : Face) (p : Vertex) : Prop :=
  ((p.x - f.v1.x) * (f.v0.y - f.v1.y) - (f.v0.x - f.v1.x) * (p.y - f.v1.y) ≤ 0 ∧
   (p.x - f.v2.x) * (f.v1.y - f.v2.y) - (f.v1.x - f.v2.x) * (p.y - f.v2.y) ≤ 0 ∧
   (p.x - f.v0.x) * (f.v2.y - f.v0.y) - (f.v2.x - f.v0.x) * (p.y - f.v0.y) ≤ 0) ∨
  (0 ≤ (p.x - f.v1.x) * (f.v0.y - f.v1.y) - (f.v0.x - f.v1.x) * (p.y - f.v1.y) ∧
   0 ≤ (p.x - f.v2.x) * (f.v1.y - f.v2.y) - (f.v1.x - f.v2.x) * (p.y - f.v2.y) ∧
   0 ≤ (p.x - f.v0.x) * (f.v2.y - f.v0.y) - (f.v2.x - f.v0.x) * (p.y - f.v0.y)  )


-- overlap f g   is a proof that f ∩ g ≠ ∅
-- the following 3 def were fixed with Gemini
def side_of (p a b : Vertex) : ℚ :=
  (p.x - a.x) * (b.y - a.y) - (b.x - a.x) * (p.y - a.y)
def edges_intersect (a1 a2 b1 b2 : Vertex) : Prop :=
  let s1 := side_of a1 b1 b2
  let s2 := side_of a2 b1 b2
  let s3 := side_of b1 a1 a2
  let s4 := side_of b2 a1 a2
  ((s1 > 0 ∧ s2 < 0) ∨ (s1 < 0 ∧ s2 > 0)) ∧
  ((s3 > 0 ∧ s4 < 0) ∨ (s3 < 0 ∧ s4 > 0))

def overlap (f g : Face) : Prop :=
  -- 1. Original check: Is any vertex of f inside g?
  (∃ v ∈ [f.v0, f.v1, f.v2], face_contains g v) ∨
  -- 2. Original check: Is any vertex of g inside f?
  (∃ v ∈ [g.v0, g.v1, g.v2], face_contains f v) ∨
  -- 3. New check: Does any edge of f intersect any edge of g?
  (∃ e_f ∈ [(f.v0, f.v1), (f.v1, f.v2), (f.v2, f.v0)],
   ∃ e_g ∈ [(g.v0, g.v1), (g.v1, g.v2), (g.v2, g.v0)],
   edges_intersect e_f.1 e_f.2 e_g.1 e_g.2)


/- Formalization of a folding Step -/

/- Step structure includes everything that specify the transition between Fold_i and Fold_i+1 -/
structure Step where
  F : Fold   -- Fold i
  G : Fold   -- Fold i+1
  c : Crease -- the line along which we fold
  map : Face → Face  -- F.faces → G.faces | f ↦ g under the form (f, g) ∈ map
  map_bijective : ∀ g ∈ G.faces, ∃! f ∈ F.faces, map f = g
  map_coherent : ∀ f ∈ F.faces, map f ≠ f → folding f (map f) c

/- Make sure that the previous face orders are compatible with the new ones
  e.g. if face_1 is above face_2 and we fold them over a crease together, then
  face_2 will be above face_1 and their order must be inverted. -/
def previous_orders_ok (F G : Fold) (map : Face → Face) : Prop :=
  ∀ fg ∈ F.f_o,
    (map fg.1 = fg.1 ∧ map fg.2 = fg.2) -- if none: nothing happens
    ∨ ((map fg.1 ≠ fg.1 ∧ map fg.2 ≠ fg.2 ∧ -- both: revert relation
      (∃ g'f' ∈ G.f_o, map fg.1 = g'f'.2 ∧ map fg.2 = g'f'.1)))
    ∨ ((map fg.1 ≠ fg.1 ∧ map fg.2 = fg.2) ∧ -- 1 moved and 2 fixed, break relation
      (map fg.1, fg.2) ∉ G.f_o)

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
  above_are_moved S.F S.map ∧
  previous_orders_ok S.F S.G S.map ∧
  new_orders_coherent S.map S.F S.G
