import Origami.FOLD.Math.EuclideanMathlib

set_option linter.style.whitespace false

noncomputable section

/--
A provable (non-tautological) solvable case of Huzita 6.
If `p1` is already on `L1`, `p2` is already on `L2`, and there exists a crease
passing through both points, then this crease satisfies the two fold constraints.
-/
theorem huzita6 (p1 p2 : Point2D) (L1 L2 : AffineSubspace ℝ Point2D)
    (hp1 : pointOnLine p1 L1) (hp2 : pointOnLine p2 L2)
    (hcrease : ∃ crease : AffineSubspace ℝ Point2D, p1 ∈ crease ∧ p2 ∈ crease) :
  ∃ crease : AffineSubspace ℝ Point2D,
    foldsPointOntoLine crease L1 p1 ∧ foldsPointOntoLine crease L2 p2 := by
  rcases hcrease with ⟨crease, hp1c, hp2c⟩
  refine ⟨crease, ?_, ?_⟩
  · simpa [foldsPointOntoLine, pointOnLine, foldOverCrease_eq_self_of_mem crease hp1c] using hp1
  · simpa [foldsPointOntoLine, pointOnLine, foldOverCrease_eq_self_of_mem crease hp2c] using hp2

end