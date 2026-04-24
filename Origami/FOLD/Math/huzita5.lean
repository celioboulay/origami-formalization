import Origami.FOLD.Math.EuclideanMathlib

noncomputable section

/--
  Axiom 5: Given two points p1 and p2 and a line L1, there is a fold
  that passes through p2 and places p1 onto L1.
-/
theorem huzita5 (p1 p2 : Point2D) (L1 : AffineSubspace ℝ Point2D) :
  ∃ crease : AffineSubspace ℝ Point2D, pointOnLine p2 crease ∧ foldsPointOntoLine crease L1 p1 := by
  -- Represents the intersection of a circle (centered at p1, radius |p1 - p2|) with L1.
  -- Depending on distance, 0, 1, or 2 folds are possible. We assume the intersection exists.
  sorry

end