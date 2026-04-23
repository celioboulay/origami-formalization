import Origami.FOLD.Properties
import Origami.FOLD.WellFormed

def pointOnEdge (p : List ℝ) (u : List ℝ) (v : List ℝ) : Prop :=
  ∃ t : ℝ, p = List.zipWith (fun a b => (1 - t) * a + t * b) u v

def pointOnFold (F : Fold) (p : List ℝ) : Prop :=
  ∃ e ∈ F.edges,
    let pu := (F.vertices.getD e.u ⟨[]⟩).coords
    let pv := (F.vertices.getD e.v ⟨[]⟩).coords
    pointOnEdge p pu pv

def pointsOnFold (F : Fold) (ps : List (List ℝ)) : Prop :=
    ∀ p ∈ ps, pointOnFold F p

def foldsEqualUpToDirection (F1 : Fold) (F2 : Fold) : Prop :=
  ∃ e1 ∈ F1.edges, ∃ e2 ∈ F1.edges,
    let pu1 := (F1.vertices.getD e1.u ⟨[]⟩).coords
    let pv1 := (F1.vertices.getD e1.v ⟨[]⟩).coords
    let pu2 := (F2.vertices.getD e2.u ⟨[]⟩).coords
    let pv2 := (F2.vertices.getD e2.v ⟨[]⟩).coords
    pointOnEdge pu2 pu1 pv1 ∧ pointOnEdge pv2 pu1 pv1
