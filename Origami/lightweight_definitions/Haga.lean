import Origami.lightweight_definitions.Huzita_axioms

open Origami


-- `huzita_2` needs `p1 ≠ p2`: a fold fixes `p` exactly when `p` lies on the crease, so if
-- `p1 = p2` then every crease through `p1` places `p1` onto `p2` and uniqueness fails.
lemma huzita_2_uniqueness (f1 f2 : Fold) (p1 p2 : Point) (hne : p1 ≠ p2) :
  f_places_p f1 p1 = p2 ∧ f_places_p f2 p1 = p2 → f1 = f2 := by
    intro h
    have hu : ∃! f : Fold, f_places_p f p1 = p2 := huzita_2 p1 p2 hne
    have h1 : f_places_p f1 p1 = p2 := by simp [h.left]
    have h2 : f_places_p f2 p1 = p2 := by simp [h.right]
    have heq : f1 = f2 := hu.unique h1 h2
    exact heq;


theorem haga_first_theorem (crease : Fold) :
  let pA : Point := ⟨1, 0⟩
  let pB : Point := ⟨(1/2 : ℚ), 1⟩
  let pC : Point := ⟨0, 0⟩
  let pLeftIntersect : Point := ⟨0, (1/3 : ℚ)⟩
  f_places_p crease pA = pB →
  let lowerEdge : Line := {a := 0, b := 1, c := 0, nontrivial := by simp, normalized := by simp}
  on_line (f_places_l crease lowerEdge) pLeftIntersect:= by
    intro pA pB pC pLeftIntersect h lowerEdge
    let alsoCrease : Fold := {a := 1, b := -2, c := 1/4, nontrivial:=by simp, normalized:=by simp}
    let alsopB : Point := f_places_p alsoCrease pA
    have pBEquiv : (alsopB = pB) := by
      unfold alsopB f_places_p alsoCrease pA pB
      simp [f_places_p, pA, pB] at *
      grind
    have creaseEquiv : alsoCrease = crease := by

      have h_combined : f_places_p alsoCrease pA = f_places_p crease pA := by
        rw [←pBEquiv] at h
        grind

      have hne : pA ≠ pB := by
        intro hEq
        have hy := congrArg Point.y hEq
        unfold pA pB at hy
        norm_num at hy

      apply huzita_2_uniqueness alsoCrease crease pA pB hne
      trivial

    have alsoOn : on_line (f_places_l alsoCrease lowerEdge) pLeftIntersect := by
      unfold on_line f_places_l alsoCrease lowerEdge pLeftIntersect
      simp; norm_num;

    rw[← creaseEquiv]
    convert alsoOn
