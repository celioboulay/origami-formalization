import Origami.FOLD.Properties
import Origami.FOLD.WellFormed
import Origami.FOLD.intersectionsCoextensivity

def huzita4PropForEdge (p u v : List ℝ) (e : Edge) (F : Fold) : Prop :=
    let pu := (F.vertices.getD e.u ⟨[]⟩).coords
    let pv := (F.vertices.getD e.v ⟨[]⟩).coords
    pointOnEdge p pu pv ∧ linesPerpendicular u v pu pv

theorem huzita4 : ∀ p u v : List ℝ, ∃ F : Fold, ∃ e ∈ F.edges, huzita4PropForEdge p u v e F := by
    sorry

