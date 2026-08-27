import Origami.lightweight_definitions.Huzita_axioms

open Origami
open scoped Classical

-- Geometric entities selected in the web interface. `p1`/`p2` are given as
-- concrete literals (rather than the opaque `axiom p1 : Point` the raw
-- generator emits) precisely because we need their coordinates: it's what
-- lets `p1 ≠ p2` be proved instead of postulated, and what lets
-- `haga_construction` below connect to `haga_first_theorem`, which is
-- stated about these same literal points.
def p1 : Point := ⟨1, 0⟩
def p2 : Point := ⟨(1/2 : ℚ), 1⟩

-- The rest of the picked construction -- the fold `huzita_2 p1 p2` actually
-- produces, and the points it made available -- kept as opaque axioms since
-- nothing downstream needs their coordinates.
axiom l1 : Line -- crease (0, 0.125) -> (1, 0.625)
axiom p3 : Point -- picked at (1, 0.625)
axiom p4 : Point -- picked at (0, 0.125)
axiom p5 : Point -- picked at (0.5, 0.375)

lemma p1_ne_p2 : p1 ≠ p2 := by
  intro hEq
  have hy := congrArg Point.y hEq
  unfold p1 p2 at hy
  norm_num at hy

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

def is_huzita_2_compliant_fold (f : Fold) (p1 p2 : Point) : Prop :=
  f_places_p f p1 = p2

-- The Huzita-2 fold placing p1 onto p2 actually exists -- unlike the
-- auto-generated preview (which only proved `True` and threw the witness
-- away), this keeps the fold and the fact that it's compliant, so
-- `haga_first_theorem` below can be applied to it directly.
theorem haga_construction : ∃ f : Fold, is_huzita_2_compliant_fold f p1 p2 := by
  obtain ⟨f1, h1, -⟩ := huzita_2 p1 p2 p1_ne_p2
  exact ⟨f1, h1⟩

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

-- The concrete payoff: the fold origami-sim actually constructed (folding
-- the picked corner p1 onto the picked point p2) provably crosses the lower
-- edge at (0, 1/3) -- no arbitrary `crease` parameter, no unproven "assume
-- such a fold exists": `haga_construction` supplies the witness,
-- `haga_first_theorem` supplies the property, definitionally about the same
-- p1/p2.
theorem haga_result :
  let pLeftIntersect : Point := ⟨0, (1/3 : ℚ)⟩
  let lowerEdge : Line := {a := 0, b := 1, c := 0, nontrivial := by simp, normalized := by simp}
  on_line (f_places_l (Classical.choose haga_construction) lowerEdge) pLeftIntersect := by
    intro pLeftIntersect lowerEdge
    exact haga_first_theorem (Classical.choose haga_construction) (Classical.choose_spec haga_construction)

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

      have hne : pA ≠ pB := by
        intro hEq
        have hy := congrArg Point.y hEq
        unfold pA pB at hy
        norm_num at hy

      apply huzita_2_uniqueness alsoCrease crease pA pB hne
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
