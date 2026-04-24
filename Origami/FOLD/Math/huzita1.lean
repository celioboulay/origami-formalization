import Origami.FOLD.Math.EuclideanMathlib

noncomputable section

/--
  Axiom 1: Given two points p1 and p2, there is a fold that passes through both of them.
-/
theorem huzita1 (p1 p2 : Point2D) (h : p1 ≠ p2) :
  ∃ crease : AffineSubspace ℝ Point2D, pointOnLine p1 crease ∧ pointOnLine p2 crease := by
  use affineSpan ℝ ({p1, p2} : Set Point2D)
  constructor
  · apply subset_affineSpan; simp
  · apply subset_affineSpan; simp

end