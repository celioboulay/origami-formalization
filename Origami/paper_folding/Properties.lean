import Mathlib

structure Vertex where -- using ℚ instead of ℝ to make things computable
  x : ℚ
  y : ℚ

structure Face where -- Faces will be triangulated
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
  reflectVertex c '' f.vertices -- the image of f.vertices by crease c

def folding (f g : Face) (c : Crease) : Prop :=
  g.vertices = reflectVertices c f

def reachable (F G : Fold) : Prop :=
  ∃ (c : Crease),
    ∀ g ∈ G.faces, (g ∈ F.faces) ∨ (
      ∃ f ∈ F.faces, folding f g c)
      -- add face order
