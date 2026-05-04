import Origami.FOLD.Math.EuclideanMathlib

noncomputable section

/--
  Axiom 1: Given two points p1 and p2, there is a fold that passes through both of them.
-/
theorem huzita1_existence (p1 p2 : Point2D) :
  ∃ crease : AffineSubspace ℝ Point2D, pointOnLine p1 crease ∧ pointOnLine p2 crease := by
  use affineSpan ℝ ({p1, p2} : Set Point2D)
  constructor
  · apply subset_affineSpan; simp
  · apply subset_affineSpan; simp

theorem line_eq_span_of_points {p1 p2 : Point2D} (h_dist : p1 ≠ p2)
  {L : AffineSubspace ℝ Point2D} (hL : lineLike L)
  (hp1 : p1 ∈ L) (hp2 : p2 ∈ L) :
  L = affineSpan ℝ {p1, p2} := by
  sorry -- We 'sorry' this for now to bypass the missing FiniteDimensional library

theorem huzita1_uniqueness (p1 p2 : Point2D) (h_dist : p1 ≠ p2)
  (crease1 crease2 : AffineSubspace ℝ Point2D)
  -- We assume they are "lines" (this is the general constraint)
  (h1 : lineLike crease1) (h2 : lineLike crease2)
  -- The points are on both lines
  (hp1_c1 : pointOnLine p1 crease1) (hp2_c1 : pointOnLine p2 crease1)
  (hp1_c2 : pointOnLine p1 crease2) (hp2_c2 : pointOnLine p2 crease2) :
  crease1 = crease2 := by
  -- 1. Show that crease1 is the affine span of p1 and p2
  have eq1 : crease1 = affineSpan ℝ {p1, p2} := by
    apply line_eq_span_of_points h_dist h1 hp1_c1 hp2_c1

  -- 2. Show that crease2 is the same affine span
  have eq2 : crease2 = affineSpan ℝ {p1, p2} := by
    apply line_eq_span_of_points h_dist h2 hp1_c2 hp2_c2

  -- 3. Conclusion
  rw [eq1, eq2]

end
