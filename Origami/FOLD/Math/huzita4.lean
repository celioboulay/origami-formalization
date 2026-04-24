import Origami.FOLD.Math.EuclideanMathlib

noncomputable section

/--
  Axiom 4: Given a point p and a line L, there is a fold perpendicular to L
  that passes through p.
-/
theorem huzita4 (p : Point2D) (L : AffineSubspace ℝ Point2D) :
  ∃ crease : AffineSubspace ℝ Point2D, pointOnLine p crease ∧ linesPerpendicular crease L := by
  -- Constructing the orthogonal affine subspace passing through `p`
  sorry

end