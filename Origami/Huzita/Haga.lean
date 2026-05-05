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
  let lowerEdge := mkLine 0 1 0
  on_line (f_places_l crease lowerEdge) pLeftIntersect:= by
    intro pA pB pC pLeftIntersect h lowerEdge
    let alsoCrease : Fold := mkLine 4 (-8) 1
    let alsopB : Point := f_places_p alsoCrease pA
    have pBEquiv : (alsopB = pB) := by
      unfold alsopB f_places_p alsoCrease pA pB mkLine
      simp [f_places_p, pA, pB] at *
      grind
    have creaseEquiv : alsoCrease = crease := by
      -- 1. Combine your calculation with the theorem's hypothesis
      have h_combined : f_places_p alsoCrease pA = f_places_p crease pA := by
        rw [←pBEquiv] at h
        grind
      -- 2. Use an injectivity or uniqueness lemma from your library
      -- This assumes that if two folds move pA to the same spot, they are the same fold.
      -- If you don't have a uniqueness lemma, you may need to prove the
      -- coefficients of the lines are equal via the formula in f_places_p.
      apply huzita_2_uniqueness alsoCrease crease pA pB
      trivial
    have alsoOn : on_line (f_places_l alsoCrease lowerEdge) pLeftIntersect := by
      unfold on_line f_places_l alsoCrease lowerEdge pLeftIntersect mkLine
      simp
      norm_num

    rw[← creaseEquiv]
    convert alsoOn
