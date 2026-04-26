import Origami.FOLD.Math.EuclideanMathlib

noncomputable section

/--
  Axiom 2: Given two points p1 and p2, there is a fold that places p1 onto p2.
  This fold is exactly the perpendicular bisector of the segment [p1, p2].
-/
theorem huzita2 (p1 p2 : Point2D) :
  ∃ crease : AffineSubspace ℝ Point2D, foldOverCrease crease p1 = p2 := by
  sorry

end