import Mathlib

set_option linter.style.emptyLine false

structure Point where
  x : ℚ
  y : ℚ

abbrev Vertex := Point -- a Vertex is a point on the inside of the unit square

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


/- Maekawa's theorem states at every vertex,
the numbers of valley and mountain folds always differ by two in either direction.
https://en.wikipedia.org/wiki/Maekawa%27s_theorem -/

/- Maekawa_condition P means that P verifies the condition
Note that this condition is necessary for the fold to be flat-foldable but no sufficient -/
def Maekawa_condition (P : CreasePattern) : Prop :=
  ∀ v ∈ P.γ,
    let M := {e ∈ P.E | (e.u = v ∨ e.v = v) ∧ e.c = Label.M}
    let n_M := M.ncard
    let V := {e ∈ P.E | (e.u = v ∨ e.v = v) ∧ e.c = Label.V}
    let n_V := V.ncard
    Int.natAbs (n_M - n_V) = 2


/- *TODO* add corollary (total number of folds at each vertex must be an even number) -/


/- Kawasaki's theorem.
A one-vertex crease pattern consists of a set of rays or creases drawn on a
flat sheet of paper, all emanating from the same point interior to the sheet. -/

/- The number of creases must be even (get from Maekawa maybe?)
Then Kawasaki's theorem states that the crease pattern may be folded flat
iff : α1 − α2 + α3 − ⋯ + α(2n-1) − α2n = 0
https://en.wikipedia.org/wiki/Kawasaki%27s_theorem -/

def Kawasaki_condition {P : CreasePattern} /- *TODO* -/
  (hγ : P.γ.ncard = 1) (h_even : Even P.V.ncard) :=
    P = P
