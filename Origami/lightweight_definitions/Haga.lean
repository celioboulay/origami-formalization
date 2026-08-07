import Origami.lightweight_definitions.Huzita_axioms

lemma huzita_2_uniqueness (f1 f2 : Fold) (p1 p2 : Point) :
  f_places_p f1 p1 = p2 ∧ f_places_p f2 p1 = p2 → f1 = f2 := by
    intro h
    have hu : ∃! f : Fold, f_places_p f p1 = p2 := by simp [huzita_2];
    have h1 : f_places_p f1 p1 = p2 := by simp [h.left]
    have h2 : f_places_p f2 p1 = p2 := by simp [h.right]
    have heq : f1 = f2 := hu.unique h1 h2
    exact heq;

def is_huzita_2_compliant_fold (f : Fold) (p1 p2 : Point) : Prop :=
  f_places_p f p1 = p2

theorem haga_first_theorem (crease : Fold) :
  let pA : Point := ⟨1, 0⟩
  let pB : Point := ⟨(1/2 : ℚ), 1⟩
  let _ : Point := ⟨0, 0⟩
  let pLeftIntersect : Point := ⟨0, (1/3 : ℚ)⟩
  is_huzita_2_compliant_fold crease pA pB →
  let lowerEdge : Line := {a := 0, b := 1, c := 0, nontrivial := by simp, normalized := by simp}
  on_line (f_places_l crease lowerEdge) pLeftIntersect:= by
    intro pA pB pC pLeftIntersect h lowerEdge
    let alsoCrease : Fold := {a := 1, b := -2, c := 1/4, nontrivial:=by simp, normalized:=by simp}
    let alsopB : Point := f_places_p alsoCrease pA
    have pBEquiv : (alsopB = pB) := by
      unfold alsopB f_places_p alsoCrease pA pB
      simp [is_huzita_2_compliant_fold, pA, pB] at *
      grind
    have creaseEquiv : alsoCrease = crease := by

      have h_combined : f_places_p alsoCrease pA = f_places_p crease pA := by
        rw [←pBEquiv] at h
        grind[is_huzita_2_compliant_fold]

      apply huzita_2_uniqueness alsoCrease crease pA pB
      trivial

    have alsoOn : on_line (f_places_l alsoCrease lowerEdge) pLeftIntersect := by
      unfold on_line f_places_l alsoCrease lowerEdge pLeftIntersect
      simp; norm_num;

    rw[← creaseEquiv]
    convert alsoOn

theorem haga_gen_equation ( n : ℚ ) (crease : Fold) :
  let pA : Point := ⟨1, 0⟩
  let pB : Point := ⟨n, 1⟩
  let pLeftIntersect : Point := ⟨0, (n / ( 2 - n ))⟩
  ( n > 0 ) ∧ ( n < 1 ) ∧ (is_huzita_2_compliant_fold crease pA pB) →
  let lowerEdge : Line := {a := 0, b := 1, c := 0, nontrivial := by simp, normalized := by simp}
  on_line (f_places_l crease lowerEdge) pLeftIntersect:= by
    intro pA pB pLeftIntersect h lowerEdge
    have h_denom : n - 1 ≠ 0 := by linarith
    have h_denom_cast : ↑n - 1 ≠ 0 := by exact_mod_cast h_denom
    have h_denom2 : 2 - n ≠ 0 := by linarith
    have h_denom2_cast : 2 - ↑n ≠ 0 := by exact_mod_cast h_denom2
    let alsoCrease : Fold := {
      a := 1,
      b := 1 / (n - 1),
      c := - (n^2 / (2 * (n - 1))),
      nontrivial := by simp,
      normalized := by grind
    }
    let alsopB : Point := f_places_p alsoCrease pA
    have pBEquiv : (alsopB = pB) := by
      unfold alsopB f_places_p alsoCrease pA pB
      simp [is_huzita_2_compliant_fold, pA, pB] at *
      field_simp
      have h_pBEquiv1 : 1 + 1 / (n - 1) ^ 2 - (2 + -(n ^ 2 / (n - 1))) = n * (1 + 1 / (n - 1) ^ 2) := by
        field_simp [h_denom]
        ring
      have h_pBEquiv2 : -((2 + -(n ^ 2 / (n - 1))) / (n - 1)) = 1 + 1 / (n - 1) ^ 2 := by
        field_simp [h_denom]
        ring
      constructor
      · exact_mod_cast h_pBEquiv1
      · exact_mod_cast h_pBEquiv2

    have creaseEquiv : alsoCrease = crease := by
      have h_combined : f_places_p alsoCrease pA = f_places_p crease pA := by
        rw [←pBEquiv] at h
        grind[is_huzita_2_compliant_fold]
      apply huzita_2_uniqueness alsoCrease crease pA pB
      grind

    have alsoOn : on_line (f_places_l alsoCrease lowerEdge) pLeftIntersect := by
      unfold on_line f_places_l alsoCrease lowerEdge pLeftIntersect
      simp
      field_simp [h_denom_cast]
      split_ifs with h_if
      · exfalso
        apply h_denom
        exact_mod_cast h_if
      · field_simp
        simp
        right
        norm_cast
        field_simp [h_denom2_cast]
        ring

    rw[← creaseEquiv]
    convert alsoOn
