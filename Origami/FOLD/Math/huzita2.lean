import Origami.FOLD.Math.EuclideanMathlib

noncomputable section

/--
  Axiom 2: Given two distinct points p1 and p2, there is a fold that places p1 onto p2.
  This fold is exactly the perpendicular bisector of the segment [p1, p2].
-/
theorem huzita2 (p1 p2 : Point2D) (h : p1 ≠ p2) :
  ∃ crease : AffineSubspace ℝ Point2D, foldOverCrease crease p1 = p2 := by
  -- In Mathlib, the perpendicular bisector between two points is an affine subspace
  -- that acts as an orthogonal symmetry exchanging them.
  sorry

end