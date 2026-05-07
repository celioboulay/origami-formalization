import Mathlib

set_option linter.style.emptyLine false

structure Point where
  x : ℚ
  y : ℚ

abbrev Vertex := Point -- the vertex of the pattern

inductive Label
  | V | M
deriving DecidableEq


structure Ray where
  u : Point
  v : Point
  c : Label


structure CreasePattern where
  γ : Set Vertex
  V : Set Point
  E : Set Ray


/- assume edges are unit square -/

-- the numbers of valley and mountain folds always differ by two

def Maekawa_condition (P : CreasePattern) : Prop :=
  ∀ v ∈ P.γ,
    let M := {e ∈ P.E | e.c = Label.M}
    let n_M := M.ncard
    let V := {e ∈ P.E | e.c = Label.V}
    let n_V := V.ncard
    Int.natAbs (n_M - n_V) = 2




-- For Kawasaki
/- A one-vertex crease pattern consists of a set of rays or creases
drawn on a flat sheet of paper, all emanating from the same
point interior to the sheet
-/

/- number of creases must be even
Then Kawasaki's theorem states that the crease pattern may be folded flat
iff : α1 − α2 + α3 − ⋯ + α(2n-1) − α2n = 0 -/

def Kawasaki_condition {P : CreasePattern}
  (hγ : P.γ.ncard = 1) (h_even : Even P.V.ncard) :=
    P = P
