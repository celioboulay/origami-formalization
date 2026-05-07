import Mathlib

set_option linter.style.whitespace false

abbrev Point := EuclideanSpace ℝ (Fin 2)

noncomputable section

/-- Build a 2D point from Cartesian coordinates. -/
def mkPoint (x y : ℝ) : Point :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm ![x, y]

/-- A point lies on the segment `[a, b]` if it is an affine interpolation of `a` and `b`. -/
def pointOnSegment (p a b : Point) : Prop :=
  ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ p = (1 - t) • a + t • b

/--
Fold of a point across a crease, defined by affine reflection when the crease is nonempty.
For the degenerate empty crease, we return the input point.
-/
def foldOverCrease (crease : AffineSubspace ℝ Point) (p : Point) : Point := by
  by_cases hne : Nonempty crease
  case pos =>
    letI : Nonempty crease := hne
    exact EuclideanGeometry.reflection crease p
  case neg =>
    exact p

lemma foldOverCrease_eq_self_of_mem (crease : AffineSubspace ℝ Point) {p : Point}
    (hp : p ∈ crease) : foldOverCrease crease p = p := by
  by_cases hne : Nonempty crease
  case pos =>
    letI : Nonempty crease := hne
    simpa [foldOverCrease, hne] using
      (EuclideanGeometry.reflection_eq_self_iff (s := crease) p).2 hp
  case neg =>
    simp [foldOverCrease, hne]

/-- Definition of a point lying on a line (an affine subspace) -/
def pointOnLine (p : Point) (L : AffineSubspace ℝ Point) : Prop :=
  p ∈ L

/-- A crease folds a point onto a target line if the reflected point is in the target line -/
def foldsPointOntoLine (crease L_target : AffineSubspace ℝ Point) (p : Point) : Prop :=
  pointOnLine (foldOverCrease crease p) L_target

/-- A crease folds line L1 onto line L2 if every point on L1 reflects to a point on L2 -/
def foldsLineOntoLine (crease L1 L2 : AffineSubspace ℝ Point) : Prop :=
  ∀ p : Point, pointOnLine p L1 → pointOnLine (foldOverCrease crease p) L2

/-- Two lines are perpendicular if their direction modules are orthogonal -/
def linesPerpendicular (L1 L2 : AffineSubspace ℝ Point) : Prop :=
  L1.direction ⟂ L2.direction

/-- Two lines are parallel if they have the same direction module. -/
def linesParallel (L1 L2 : AffineSubspace ℝ Point) : Prop :=
  L1.direction = L2.direction

/-- Minimal geometric non-degeneracy for an affine line-like object in 2D. -/
def lineLike (L : AffineSubspace ℝ Point) : Prop :=
  Nonempty L ∧ L.direction ≠ ⊥

end
