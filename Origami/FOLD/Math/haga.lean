import Origami.FOLD.Math.EuclideanMathlib
import Mathlib.Data.Real.Basic

noncomputable section

/--
Haga's first theorem in the new geometric layer.
If a crease sends `A = (1, 0)` to `B = (1/2, 1)`, then for `C = (1, 1)`
the point `(0, 2/3)` lies on the segment between `B` and the reflected point `C'`.
-/
theorem haga_first_theorem (crease : AffineSubspace ℝ Point2D) :
  let pA : Point2D := mkPoint2D 1 0
  let pB : Point2D := mkPoint2D (1 / 2) 1
  let pC : Point2D := mkPoint2D 0 0
  let pLeftIntersect : Point2D := mkPoint2D 0 (1 / 3)
  foldOverCrease crease pA = pB →
  let pCPrime : Point2D := foldOverCrease crease pC
  pointOnSegment pLeftIntersect pB pCPrime := by
  intro pA pB pC pLeftIntersect hFold pCPrime
  have creaseNotEmpty : Nonempty crease := by sorry -- Huzita 2 goes here
  unfold pCPrime
  let midpt := pA + ((1/2 : ℝ) • (pB - pA))
  rw[foldOverCrease]
  simp [pA, pB, pC, pLeftIntersect, pointOnSegment, creaseNotEmpty, hFold] at *
    -- apply EuclideanGeometry.midpoint_reflection_mem
end
