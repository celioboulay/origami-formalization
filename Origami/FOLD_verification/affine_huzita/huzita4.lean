import Origami.FOLD.Math.EuclideanMathlib

noncomputable section

/--
  Axiom 4: Given a point p and a line L, there is a fold perpendicular to L
  that passes through p.
-/
theorem huzita4_existence (p : Point2D) (L : AffineSubspace ℝ Point2D) :
  ∃ crease : AffineSubspace ℝ Point2D, pointOnLine p crease ∧ linesPerpendicular crease L := by
  -- Constructing the orthogonal affine subspace passing through `p`
  sorry

theorem huzita4_uniqueness (p : Point2D) (L : AffineSubspace ℝ Point2D)
  (crease1 crease2 : AffineSubspace ℝ Point2D)
  -- We assume they are "lines" (this is the general constraint)
  (h1 : lineLike crease1) (h2 : lineLike crease2)
  -- The points are on both lines
  (hpc1 : pointOnLine p crease1)
  (hpc2 : pointOnLine p crease2)
  (hlc1 : linesPerpendicular crease1 L)
  (hlc2 : linesPerpendicular crease2 L) :
  crease1 = crease2 := by
  sorry

end
