import Origami.FOLD.Data.intersectionsCoextensivity
import Mathlib.Data.Real.Basic

/--
  Haga's first theorem:
  Folding the bottom-right corner A(1, 0) of a unit square to the midpoint
  of the top edge B(1/2, 1) reflects the right edge AC (where C is (1, 1)).
  The new reflected edge BC' intersects the left edge of the square at exactly (0, 2/3).
-/
theorem haga_first_theorem (crease_a crease_b : List ℝ) (h_not_empty : crease_a ≠ []) :
  let pA : List ℝ := [1, 0]
  let pB : List ℝ := [1/2, 1]
  let pC : List ℝ := [1, 1]
  let p_left_intersect : List ℝ := [0, 2/3]
  -- If the crease defined by (crease_a, crease_b) reflects pA onto pB
  flipOverLine pA crease_a crease_b = pB →
  -- Then the reflected point C' is such that the left intersection point
  -- lies exactly on the segment [pB, pC_prime]
  let pC_prime := flipOverLine pC crease_a crease_b;
  pointOnEdge p_left_intersect pB pC_prime := by
  intros
  sorry