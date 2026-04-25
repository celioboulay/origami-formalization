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

/-- Well-formedness specialized to the 2D bridge assumptions. -/
def WellFormed2D (F : Fold) : Prop :=
  WellFormed F ∧ FoldVerticesAre2D F

/-- `BridgeReady` is just the 2D-specialized well-formedness package. -/
lemma bridgeReady_iff_wellFormed2D (F : Fold) :
    BridgeReady F ↔ WellFormed2D F := by
  rfl

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

lemma listGet?_isSome_iff {xs : List α} {i : Nat} :
    (listGet? xs i).isSome ↔ i < xs.length := by
  by_cases h : i < xs.length
  · simp [listGet?, h]
  · simp [listGet?, h]

lemma listToPoint2D_isSome_iff_length_eq_two {xs : List ℝ} :
    (listToPoint2D xs).isSome ↔ xs.length = 2 := by
  cases xs with
  | nil => simp [listToPoint2D]
  | cons x xs =>
      cases xs with
      | nil => simp [listToPoint2D]
      | cons y xs =>
          cases xs with
          | nil => simp [listToPoint2D]
          | cons z zs => simp [listToPoint2D]

lemma vertexToPoint2D_isSome_iff (v : Vertex) :
    (vertexToPoint2D v).isSome ↔ VertexIs2D v := by
  simpa [vertexToPoint2D, VertexIs2D] using
    (listToPoint2D_isSome_iff_length_eq_two (xs := v.coords))

lemma edgeToPoints_isSome_of_wellIndexed_and_2d {F : Fold} {e : Edge}
    (hIdx : EdgeWellIndexed F e) (h2D : FoldVerticesAre2D F) :
    (edgeToPoints F e).isSome := by
  let uVertex : Vertex := F.vertices.get ⟨e.u, hIdx.1⟩
  let vVertex : Vertex := F.vertices.get ⟨e.v, hIdx.2⟩
  have huLookup : listGet? F.vertices e.u = some uVertex := by
    simp [listGet?, hIdx.1, uVertex]
  have hvLookup : listGet? F.vertices e.v = some vVertex := by
    simp [listGet?, hIdx.2, vVertex]
  have hu2D : VertexIs2D uVertex := by
    exact h2D uVertex (List.get_mem _ _)
  have hv2D : VertexIs2D vVertex := by
    exact h2D vVertex (List.get_mem _ _)
  have huPointSome : (vertexToPoint2D uVertex).isSome :=
    (vertexToPoint2D_isSome_iff uVertex).2 hu2D
  have hvPointSome : (vertexToPoint2D vVertex).isSome :=
    (vertexToPoint2D_isSome_iff vVertex).2 hv2D
  rcases Option.isSome_iff_exists.mp huPointSome with ⟨uPoint, huPoint⟩
  rcases Option.isSome_iff_exists.mp hvPointSome with ⟨vPoint, hvPoint⟩
  refine Option.isSome_iff_exists.mpr ?_
  refine ⟨(uPoint, vPoint), ?_⟩
  simp [edgeToPoints, huLookup, hvLookup, huPoint, hvPoint]

lemma edgeToPoints_isSome_of_bridgeReady {F : Fold} {e : Edge}
    (hReady : BridgeReady F) (he : e ∈ F.edges) :
    (edgeToPoints F e).isSome := by
  rcases hReady with ⟨hWF, h2D⟩
  exact edgeToPoints_isSome_of_wellIndexed_and_2d
    (edgeWellIndexed_of_mem_wellFormed hWF he) h2D

lemma edgeToCrease_isSome_of_bridgeReady {F : Fold} {e : Edge}
    (hReady : BridgeReady F) (he : e ∈ F.edges) :
    (edgeToCrease F e).isSome := by
  rcases Option.isSome_iff_exists.mp
      (edgeToPoints_isSome_of_bridgeReady hReady he) with ⟨uv, huv⟩
  rcases uv with ⟨u, v⟩
  refine Option.isSome_iff_exists.mpr ?_
  refine ⟨affineSpan ℝ ({u, v} : Set Point2D), ?_⟩
  simp [edgeToCrease, huv]

lemma edgeToCrease_exists_of_bridgeReady {F : Fold} {e : Edge}
    (hReady : BridgeReady F) (he : e ∈ F.edges) :
    ∃ crease : AffineSubspace ℝ Point2D, edgeToCrease F e = some crease := by
  exact Option.isSome_iff_exists.mp (edgeToCrease_isSome_of_bridgeReady hReady he)

end Origami.FOLD.Bridge
