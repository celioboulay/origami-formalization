import Origami.FOLD.Math.EuclideanMathlib

noncomputable section

/--
  Axiom 2: Given two points p1 and p2, there is a fold that places p1 onto p2.
  This fold is exactly the perpendicular bisector of the segment [p1, p2].
-/
theorem huzita2_existence (p1 p2 : Point2D) :
  ∃ crease : AffineSubspace ℝ Point2D, foldOverCrease crease p1 = p2 := by
  -- Use the midpoint as the base point and the orthogonal complement of the span of (p2 - p1) as the direction
  let perpCrease := AffineSubspace.mk' (midpoint ℝ p1 p2) (Submodule.span ℝ {p2 -ᵥ p1})ᗮ
  use perpCrease
  rw[foldOverCrease]
  rw [dif_pos (show Nonempty perpCrease from ⟨midpoint ℝ p1 p2, AffineSubspace.self_mem_mk' _ _⟩)]
  sorry

theorem huzita2_uniqueness (p1 p2 : Point2D) (h_dist : p1 ≠ p2)
  (crease1 crease2 : AffineSubspace ℝ Point2D)
  -- We assume they are "lines" (this is the general constraint)
  (h1 : lineLike crease1) (h2 : lineLike crease2)
  -- The points are on both lines
  (hp1_c1 : foldOverCrease crease1 p1 = p2)
  (hp1_c2 : foldOverCrease crease2 p1 = p2 ) :
  crease1 = crease2 := by
  sorry
end
