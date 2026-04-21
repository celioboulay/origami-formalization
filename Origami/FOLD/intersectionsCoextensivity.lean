import Origami.FOLD.Properties
import Origami.FOLD.WellFormed

def pointOnEdge (p : List ℝ) (u : List ℝ) (v : List ℝ) : Prop :=
  ∃ t : ℝ, p = List.zipWith (fun a b => (1 - t) * a + t * b) pu pv

def pointOnFold (F : Fold) (p : List ℝ) : Prop :=
  ∃ e ∈ F.edges,
    let pu := (F.vertices.get! e.u).coords
    let pv := (F.vertices.get! e.v).coords
    pointOnEdge p pu pv

def pointsOnFold (F : Fold) (ps : List (List ℝ)) : Prop :=
    ∀ p ∈ ps, pointOnFold F p

def foldsEqualUpToDirection (F1 : Fold) (F1 : Fold) : Prop :=
  ∃ e1 ∈ F1.edges, ∃ e2 ∈ F1.edges,
    let pu1 := (F1.vertices.get! e.u).coords
    let pv1 := (F1.vertices.get! e.v).coords
    let pu2 := (F2.vertices.get! e.u).coords
    let pv2 := (F2.vertices.get! e.v).coords
    pointOnEdge pu2 pu1 pv1 and pointOnEdge pv2 pu1 pv1
