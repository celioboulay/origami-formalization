import Origami.FOLD.Properties
import Origami.FOLD.WellFormed

def pointOnFold (F : Fold) (p : List ℝ) : Prop :=
  ∃ e ∈ F.edges,
    let pu := (F.vertices.get! e.u).coords
    let pv := (F.vertices.get! e.v).coords
    ∃ t : ℝ, p = List.zipWith (fun a b => (1 - t) * a + t * b) pu pv

def pointsOnFold (F : Fold) (ps : List (List ℝ)) : Prop :=
    ∀ p ∈ ps, pointOnFold F p
