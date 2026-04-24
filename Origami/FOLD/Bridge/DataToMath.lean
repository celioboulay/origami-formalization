import Origami.FOLD.Data.Properties
import Origami.FOLD.Data.WellFormed
import Origami.FOLD.Math.EuclideanMathlib

noncomputable section

namespace Origami.FOLD.Bridge

/-- A raw coordinate list can be interpreted as a 2D point iff it has two entries. -/
def listToPoint2D : List ℝ → Option Point2D
  | [x, y] => some (mkPoint2D x y)
  | _ => none

/-- Convert one `Vertex` from the FOLD layer to a 2D point in the math layer. -/
def vertexToPoint2D (v : Vertex) : Option Point2D :=
  listToPoint2D v.coords

/-- A vertex is 2D when its coordinate list has length 2. -/
def VertexIs2D (v : Vertex) : Prop :=
  v.coords.length = 2

/-- All vertices of a fold have 2D coordinates. -/
def FoldVerticesAre2D (F : Fold) : Prop :=
  ∀ v ∈ F.vertices, VertexIs2D v

/-- Minimal assumptions to bridge one parsed fold into the 2D geometric layer. -/
def BridgeReady (F : Fold) : Prop :=
  WellFormed F ∧ FoldVerticesAre2D F

/-- Safe list lookup by index. -/
def listGet? (xs : List α) (i : Nat) : Option α :=
  if h : i < xs.length then some (xs.get ⟨i, h⟩) else none

/-- Decode one edge as its endpoint points. -/
def edgeToPoints (F : Fold) (e : Edge) : Option (Point2D × Point2D) := do
  let uVertex ← listGet? F.vertices e.u
  let vVertex ← listGet? F.vertices e.v
  let u ← vertexToPoint2D uVertex
  let v ← vertexToPoint2D vVertex
  pure (u, v)

/-- Decode one edge as the geometric crease (line through the two endpoints). -/
def edgeToCrease (F : Fold) (e : Edge) : Option (AffineSubspace ℝ Point2D) := do
  let (u, v) ← edgeToPoints F e
  pure (affineSpan ℝ ({u, v} : Set Point2D))

/-- Decode all FOLD edges that can be interpreted as geometric creases. -/
def foldToCreases (F : Fold) : List (AffineSubspace ℝ Point2D) :=
  F.edges.filterMap (edgeToCrease F)

lemma listToPoint2D_some_iff {xs : List ℝ} {p : Point2D} :
    listToPoint2D xs = some p ↔ ∃ x y : ℝ, xs = [x, y] ∧ p = mkPoint2D x y := by
  cases xs with
  | nil => simp [listToPoint2D]
  | cons x xs =>
      cases xs with
      | nil => simp [listToPoint2D]
      | cons y xs =>
          cases xs with
          | nil => simp [listToPoint2D, eq_comm]
          | cons z zs => simp [listToPoint2D]

lemma vertexToPoint2D_some_iff (v : Vertex) {p : Point2D} :
    vertexToPoint2D v = some p ↔ ∃ x y : ℝ, v.coords = [x, y] ∧ p = mkPoint2D x y := by
  simpa [vertexToPoint2D] using (listToPoint2D_some_iff (xs := v.coords) (p := p))

lemma edgeToCrease_eq_some_of_edgeToPoints_eq_some {F : Fold} {e : Edge} {u v : Point2D}
    (h : edgeToPoints F e = some (u, v)) :
    edgeToCrease F e = some (affineSpan ℝ ({u, v} : Set Point2D)) := by
  simp [edgeToCrease, h]

end Origami.FOLD.Bridge


