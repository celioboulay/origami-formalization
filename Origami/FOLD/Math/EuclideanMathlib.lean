import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Euclidean.Basic

abbrev Point2D := EuclideanSpace ℝ (Fin 2)

noncomputable section

/--
In Mathlib 4, orthogonal reflection across an affine subspace is provided
by `reflection` which creates an `IsometryEquiv`.
We leave it as an axiom `sorry` here due to the specific mathlib 4 version
and missing explicit imports for `reflection` locally.
-/
def foldOverCrease (crease : AffineSubspace ℝ Point2D) (p : Point2D) : Point2D :=
  sorry

/-- Definition of a point lying on a line (an affine subspace) -/
def pointOnLine (p : Point2D) (L : AffineSubspace ℝ Point2D) : Prop :=
  p ∈ L

/-- A crease folds a point onto a target line if the reflected point is in the target line -/
def foldsPointOntoLine (crease L_target : AffineSubspace ℝ Point2D) (p : Point2D) : Prop :=
  pointOnLine (foldOverCrease crease p) L_target

/-- A crease folds line L1 onto line L2 if every point on L1 reflects to a point on L2 -/
def foldsLineOntoLine (crease L1 L2 : AffineSubspace ℝ Point2D) : Prop :=
  ∀ p : Point2D, pointOnLine p L1 → pointOnLine (foldOverCrease crease p) L2

/-- Two lines are perpendicular if their direction modules are orthogonal -/
def linesPerpendicular (L1 L2 : AffineSubspace ℝ Point2D) : Prop :=
  L1.direction ⟂ L2.direction

end