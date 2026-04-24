import Origami.FOLD.Properties
import Origami.FOLD.WellFormed
import Origami.FOLD.intersectionsCoextensivity

def huzita7PropForEdge (p l11 l12 l21 l22 : List ℝ) (e : Edge) (F : Fold) : Prop :=
    let pu := (F.vertices.getD e.u ⟨[]⟩).coords
    let pv := (F.vertices.getD e.v ⟨[]⟩).coords
    pointOnLineOnceFoldedForEdge p l11 l12 e F ∧ linesPerpendicular pu pv l21 l22

theorem huzita7 : ∀ p l11 l12 l21 l22 : List ℝ, ¬ linesParallel l11 l12 l21 l22 → ∃ F : Fold, ∃ e ∈ F.edges, huzita7PropForEdge p l11 l12 l21 l22 e F := by
    sorry
