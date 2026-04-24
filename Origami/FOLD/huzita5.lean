import Origami.FOLD.Properties
import Origami.FOLD.WellFormed
import Origami.FOLD.intersectionsCoextensivity

def huzita5PropForEdge (p : List ℝ) (e : Edge) (F : Fold) : Prop :=
    let pu := (F.vertices.getD e.u ⟨[]⟩).coords
    let pv := (F.vertices.getD e.v ⟨[]⟩).coords
    pointOnEdge p pu pv

theorem huzita5 : ∀ p1 p2 l1 l2 : List ℝ, ∃ F : Fold, ∃ e ∈ F.edges, pointOnLineOnceFoldedForEdge p1 l1 l2 e F ∧ huzita5PropForEdge p2 e F := by
    sorry
