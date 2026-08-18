import Origami.lightweight_definitions.Huzita_axioms

namespace Origami

theorem huzita_5_iff (p₁ p₂ : Point) (l₁ : Line) :
    (∃ f : Fold, f_through_p f p₂ ∧ on_line l₁ (f_places_p f p₁))
      ↔ dist2_line l₁ p₂ ≤ dist2 p₁ p₂ := by
  refine ⟨?_, huzita_5 p₁ p₂ l₁⟩
  rintro ⟨f, hthrough, hon⟩
  have hfix : f_places_p f p₂ = p₂ := (f_places_p_eq_self_iff f p₂).2 hthrough
  have hd : dist2 p₂ (f_places_p f p₁) = dist2 p₂ p₁ := by
    have hiso := f_places_p_dist2 f p₂ p₁
    rwa [hfix] at hiso
  calc dist2_line l₁ p₂ ≤ dist2 p₂ (f_places_p f p₁) := dist2_line_le_dist2 hon
    _ = dist2 p₂ p₁ := hd
    _ = dist2 p₁ p₂ := dist2_comm p₂ p₁

def xAxis : Line :=
  { a := 0, b := 1, c := 0, nontrivial := Or.inr one_ne_zero, normalized := Or.inr ⟨rfl, rfl⟩ }

def yAxis : Line :=
  { a := 1, b := 0, c := 0, nontrivial := Or.inl one_ne_zero, normalized := Or.inl rfl }

def yEqNegTwo : Line :=
  { a := 0, b := 1, c := 2, nontrivial := Or.inr one_ne_zero, normalized := Or.inr ⟨rfl, rfl⟩ }

theorem xAxis_ne_yAxis : xAxis ≠ yAxis := by
  intro hEq
  have : (0 : ℝ) = 1 := congrArg Line.a hEq
  exact zero_ne_one this

theorem huzita_2_not_unique_of_eq : ¬ ∀ p₁ p₂ : Point, ∃! f : Fold, f_places_p f p₁ = p₂ := by
  intro hAll
  obtain ⟨f, _, huniq⟩ := hAll ⟨0, 0⟩ ⟨0, 0⟩
  have h₁ : f_places_p xAxis ⟨0, 0⟩ = ⟨0, 0⟩ := by
    rw [f_places_p_eq_self_iff]; unfold f_through_p xAxis; norm_num
  have h₂ : f_places_p yAxis ⟨0, 0⟩ = ⟨0, 0⟩ := by
    rw [f_places_p_eq_self_iff]; unfold f_through_p yAxis; norm_num
  exact xAxis_ne_yAxis ((huniq _ h₁).trans (huniq _ h₂).symm)

theorem huzita_3_not_unique : ¬ ∀ l₁ l₂ : Line, ∃! f : Fold, f_places_l f l₁ = l₂ := by
  intro hAll
  obtain ⟨f, _, huniq⟩ := hAll xAxis xAxis
  have h₁ : f_places_l xAxis xAxis = xAxis := f_places_l_self xAxis
  have h₂ : f_places_l yAxis xAxis = xAxis := by
    refine f_places_l_eq_of_scale (k := 1) one_ne_zero ?_ ?_ ?_ <;> unfold xAxis yAxis <;> norm_num
  exact xAxis_ne_yAxis ((huniq _ h₁).trans (huniq _ h₂).symm)

def diagPos : Line :=
  { a := 1, b := -1, c := 0, nontrivial := Or.inl one_ne_zero, normalized := Or.inl rfl }

def diagNeg : Line :=
  { a := 1, b := 1, c := 0, nontrivial := Or.inl one_ne_zero, normalized := Or.inl rfl }

theorem huzita_3_two_bisectors :
    ∃ f g : Fold, f ≠ g ∧ f_places_l f xAxis = yAxis ∧ f_places_l g xAxis = yAxis := by
  refine ⟨diagPos, diagNeg, ?_, ?_, ?_⟩
  · intro hEq
    have hb := congrArg Line.b hEq
    unfold diagPos diagNeg at hb
    norm_num at hb
  · refine f_places_l_eq_of_scale (k := 2) (by norm_num) ?_ ?_ ?_ <;>
      unfold diagPos xAxis yAxis <;> norm_num
  · refine f_places_l_eq_of_scale (k := -2) (by norm_num) ?_ ?_ ?_ <;>
      unfold diagNeg xAxis yAxis <;> norm_num

theorem huzita_7_parallel_none {p : Point} {l₁ l₂ : Line} (hpar : parallel l₁ l₂)
    (hp : ¬ on_line l₁ p) :
    ¬ ∃ f : Fold, on_line l₁ (f_places_p f p) ∧ perpendicular f l₂ := by
  rintro ⟨f, hinc, hperp⟩
  obtain ⟨ha, hb⟩ := (parallel_iff_normals_eq l₁ l₂).1 hpar
  unfold perpendicular at hperp
  have hperp' : l₁.a * f.a + l₁.b * f.b = 0 := by rw [ha, hb]; linarith
  rw [on_line_f_places_p, hperp', mul_zero] at hinc
  exact hp ((mul_eq_zero.1 hinc).resolve_left f.sq_add_sq_ne_zero)

theorem huzita_7_parallel_on_not_unique {p : Point} {l₁ l₂ : Line} (hpar : parallel l₁ l₂)
    (hp : on_line l₁ p) :
    ¬ ∃! f : Fold, on_line l₁ (f_places_p f p) ∧ perpendicular f l₂ := by
  rintro ⟨f, -, huniq⟩
  obtain ⟨ha, hb⟩ := (parallel_iff_normals_eq l₁ l₂).1 hpar
  have hnt := Line.perp_nontrivial l₂
  unfold on_line at hp
  rw [ha, hb] at hp
  have key : ∀ c : ℝ, on_line l₁ (f_places_p (mk_line (-l₂.b) l₂.a c hnt) p)
      ∧ perpendicular (mk_line (-l₂.b) l₂.a c hnt) l₂ := by
    intro c
    refine ⟨?_, ?_⟩
    · rw [on_line_f_places_p_mk_line, ha, hb]
      linear_combination ((-l₂.b) ^ 2 + l₂.a ^ 2) * hp
    · obtain ⟨k, hk, hka, hkb, -⟩ := exists_scale_mk_line (-l₂.b) l₂.a c hnt
      unfold perpendicular
      rw [hka, hkb]; ring
  exact mk_line_ne_of_c_ne hnt (by norm_num : (0 : ℝ) ≠ 1)
    ((huniq _ (key 0)).trans (huniq _ (key 1)).symm)

theorem huzita_7_iff (p : Point) (l₁ l₂ : Line) :
    (∃! f : Fold, on_line l₁ (f_places_p f p) ∧ perpendicular f l₂) ↔ ¬ parallel l₁ l₂ := by
  refine ⟨fun hex hpar => ?_, huzita_7 p l₁ l₂⟩
  by_cases hp : on_line l₁ p
  · exact huzita_7_parallel_on_not_unique hpar hp hex
  · exact huzita_7_parallel_none hpar hp hex.exists

theorem huzita_1_not_unique_of_eq :
    ¬ ∀ p₁ p₂ : Point, ∃! f : Fold, f_through_p f p₁ ∧ f_through_p f p₂ := by
  intro hAll
  obtain ⟨f, _, huniq⟩ := hAll ⟨0, 0⟩ ⟨0, 0⟩
  have h₁ : f_through_p xAxis ⟨0, 0⟩ ∧ f_through_p xAxis ⟨0, 0⟩ := by
    unfold f_through_p xAxis; norm_num
  have h₂ : f_through_p yAxis ⟨0, 0⟩ ∧ f_through_p yAxis ⟨0, 0⟩ := by
    unfold f_through_p yAxis; norm_num
  exact xAxis_ne_yAxis ((huniq _ h₁).trans (huniq _ h₂).symm)

theorem huzita_7_needs_not_parallel :
    ¬ ∀ (p : Point) (l₁ l₂ : Line),
        ∃! f : Fold, on_line l₁ (f_places_p f p) ∧ perpendicular f l₂ := by
  intro hAll
  obtain ⟨f, _, huniq⟩ := hAll ⟨0, 0⟩ xAxis xAxis
  have key : ∀ c : ℝ, on_line xAxis (f_places_p (mk_line 1 0 c (Or.inl one_ne_zero)) ⟨0, 0⟩)
      ∧ perpendicular (mk_line 1 0 c (Or.inl one_ne_zero)) xAxis := by
    intro c
    refine ⟨?_, ?_⟩
    · rw [on_line_f_places_p_mk_line]; unfold xAxis; norm_num
    · obtain ⟨k, hk, hka, hkb, _⟩ := exists_scale_mk_line 1 0 c (Or.inl one_ne_zero)
      unfold perpendicular xAxis
      rw [hka, hkb]; ring
  have hne : mk_line 1 0 0 (Or.inl one_ne_zero) ≠ mk_line 1 0 (-1) (Or.inl one_ne_zero) := by
    intro hEq
    have hc := congrArg Line.c hEq
    norm_num [mk_line] at hc
  exact hne ((huniq _ (key 0)).trans (huniq _ (key (-1))).symm)

theorem huzita_6_needs_not_parallel :
    ¬ ∀ (p₁ p₂ : Point) (l₁ l₂ : Line),
        ∃ f : Fold, on_line l₁ (f_places_p f p₁) ∧ on_line l₂ (f_places_p f p₂) := by
  intro hAll
  obtain ⟨f, h₁, h₂⟩ := hAll ⟨0, 1⟩ ⟨0, 2⟩ xAxis yEqNegTwo
  rw [on_line_f_places_p] at h₁ h₂
  norm_num [xAxis, yEqNegTwo] at h₁ h₂
  nlinarith [f.sq_add_sq_pos, sq_nonneg f.a, sq_nonneg f.b, h₁, h₂]

end Origami
