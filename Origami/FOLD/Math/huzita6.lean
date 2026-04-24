import Origami.FOLD.Math.EuclideanMathlib

noncomputable section

/--
  Axiom 6: Given two points p1 and p2 and two lines L1 and L2, there is a fold
  that places p1 onto L1 and p2 onto L2 simultaneously.
-/
theorem huzita6 (p1 p2 : Point2D) (L1 L2 : AffineSubspace ℝ Point2D) :
  ∃ crease : AffineSubspace ℝ Point2D,
    foldsPointOntoLine crease L1 p1 ∧ foldsPointOntoLine crease L2 p2 := by
  sorry

end