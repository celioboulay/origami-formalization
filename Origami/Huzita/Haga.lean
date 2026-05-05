import Mathlib
import Origami.Huzita.Structures
import Origami.Huzita.Axioms

def mkLine (a b c : ℚ) : Line :=
  { a := a,
    b := b,
    c := c,
    nontrivial := by revert a b; decide,
    normalized := by revert a b; decide }

theorem haga_first_theorem (crease : Fold) :
  let pA : Point := ⟨1, 0⟩
  let pB : Point := ⟨(1/2 : ℚ), 1⟩
  let pC : Point := ⟨0, 0⟩
  let pLeftIntersect : Point := ⟨0, (1/3 : ℚ)⟩
  f_places_p crease pA = pB →
  let upperEdge := mkLine 0 1 0
  on_line (f_places_l crease upperEdge) pLeftIntersect:= by
    intro pA pB pC pLeftIntersect h upperEdge
    let alsoCrease : Fold := mkLine 4 (-8) 1
    let alsopB : Point := f_places_p alsoCrease pA
    have pBEquiv : (alsopB = pB) := by
      unfold alsopB f_places_p alsoCrease pA pB mkLine
      simp [f_places_p, pA, pB] at *
      grind
    have creaseEquiv : (alsoCrease = crease) := by
      sorry
    have alsoOn : on_line (f_places_l alsoCrease upperEdge) pLeftIntersect := by
      unfold on_line f_places_l alsoCrease upperEdge pLeftIntersect mkLine
      norm_num
      sorry

    rw[← creaseEquiv]
    exact alsoOn
