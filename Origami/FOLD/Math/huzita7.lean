import Origami.FOLD.Math.EuclideanMathlib

noncomputable section

/--
  Axiom 7: Given a point p and two lines L1 and L2, there is a fold
  perpendicular to L2 that places p onto L1.
-/
theorem huzita7 (p : Point2D) (L1 L2 : AffineSubspace ℝ Point2D)
    (hParallel : linesParallel L1 L2) :
  ∃ crease : AffineSubspace ℝ Point2D,
    linesPerpendicular crease L2 ∧ foldsPointOntoLine crease L1 p := by
  sorry

end