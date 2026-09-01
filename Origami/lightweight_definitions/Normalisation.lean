import Origami.lightweight_definitions.Structures

attribute [ext] Point

theorem Line.ext' {l₁ l₂ : Line} (ha : l₁.a = l₂.a) (hb : l₁.b = l₂.b) (hc : l₁.c = l₂.c) :
    l₁ = l₂ := by
  cases l₁; cases l₂
  simp only at ha hb hc
  subst ha; subst hb; subst hc
  rfl

theorem Line.sq_add_sq_pos (l : Line) : 0 < l.a ^ 2 + l.b ^ 2 := by
  rcases l.nontrivial with h | h <;> positivity

theorem Line.sq_add_sq_ne_zero (l : Line) : l.a ^ 2 + l.b ^ 2 ≠ 0 :=
  ne_of_gt l.sq_add_sq_pos

theorem Point.sub_ne_zero_or {p₁ p₂ : Point} (h : p₁ ≠ p₂) :
    p₂.x - p₁.x ≠ 0 ∨ p₂.y - p₁.y ≠ 0 := by
  by_contra hcon
  push Not at hcon
  exact h (Point.ext (by linarith [hcon.1]) (by linarith [hcon.2]))

theorem Point.sub_sq_add_sq_ne_zero {p₁ p₂ : Point} (h : p₁ ≠ p₂) :
    (p₂.x - p₁.x) ^ 2 + (p₂.y - p₁.y) ^ 2 ≠ 0 := by
  rcases Point.sub_ne_zero_or h with h' | h' <;> positivity

theorem Line.perp_nontrivial (l : Line) : -l.b ≠ 0 ∨ l.a ≠ 0 := by
  rcases l.nontrivial with h | h
  · exact Or.inr h
  · exact Or.inl (neg_ne_zero.2 h)

namespace Origami

theorem f_through_p_iff_on_line (f : Fold) (p : Point) : f_through_p f p ↔ on_line f p := Iff.rfl

noncomputable def mk_line (a b c : ℝ) (_h : a ≠ 0 ∨ b ≠ 0) : Line :=
  if a ≠ 0 then
    { a := 1, b := b / a, c := c / a
      nontrivial := Or.inl one_ne_zero
      normalized := Or.inl rfl }
  else
    { a := 0, b := 1, c := c / b
      nontrivial := Or.inr one_ne_zero
      normalized := Or.inr ⟨rfl, rfl⟩ }

theorem mk_line_congr {a b c a' b' c' : ℝ} {h : a ≠ 0 ∨ b ≠ 0} {h' : a' ≠ 0 ∨ b' ≠ 0}
    (ha : a = a') (hb : b = b') (hc : c = c') : mk_line a b c h = mk_line a' b' c' h' := by
  subst ha; subst hb; subst hc; rfl

theorem exists_scale_mk_line (a b c : ℝ) (h : a ≠ 0 ∨ b ≠ 0) :
    ∃ k : ℝ, k ≠ 0 ∧ (mk_line a b c h).a = k * a ∧ (mk_line a b c h).b = k * b ∧
      (mk_line a b c h).c = k * c := by
  unfold mk_line
  split_ifs with ha
  · exact ⟨a⁻¹, inv_ne_zero ha, by field_simp, by field_simp, by field_simp⟩
  · rw [not_not] at ha
    have hb : b ≠ 0 := h.resolve_left (by simp [ha])
    exact ⟨b⁻¹, inv_ne_zero hb, by simp [ha], by field_simp, by field_simp⟩

@[simp]
theorem on_line_mk_line (a b c : ℝ) (h : a ≠ 0 ∨ b ≠ 0) (p : Point) :
    on_line (mk_line a b c h) p ↔ a * p.x + b * p.y + c = 0 := by
  obtain ⟨k, hk, ha, hb, hc⟩ := exists_scale_mk_line a b c h
  unfold on_line
  rw [ha, hb, hc]
  constructor
  · intro hp
    have hkp : k * (a * p.x + b * p.y + c) = 0 := by linear_combination hp
    exact (mul_eq_zero.1 hkp).resolve_left hk
  · intro hp; linear_combination k * hp

@[simp]
theorem f_through_p_mk_line (a b c : ℝ) (h : a ≠ 0 ∨ b ≠ 0) (p : Point) :
    f_through_p (mk_line a b c h) p ↔ a * p.x + b * p.y + c = 0 :=
  on_line_mk_line a b c h p

end Origami

theorem Line.eq_of_scale {l₁ l₂ : Line} {k : ℝ} (hk : k ≠ 0)
    (ha : l₁.a = k * l₂.a) (hb : l₁.b = k * l₂.b) (hc : l₁.c = k * l₂.c) : l₁ = l₂ := by
  have hk1 : k = 1 := by
    rcases l₁.normalized with h₁ | ⟨h₁a, h₁b⟩ <;> rcases l₂.normalized with h₂ | ⟨h₂a, h₂b⟩
    · rw [h₁, h₂, mul_one] at ha; exact ha.symm
    · rw [h₁, h₂a, mul_zero] at ha; exact absurd ha one_ne_zero
    · rw [h₁a, h₂, mul_one] at ha; exact absurd ha.symm hk
    · rw [h₁b, h₂b, mul_one] at hb; exact hb.symm
  subst hk1
  exact Line.ext' (by simpa using ha) (by simpa using hb) (by simpa using hc)

namespace Origami

theorem mk_line_eq_of_scale {a b c : ℝ} {h : a ≠ 0 ∨ b ≠ 0} {m : Line} {k : ℝ} (hk : k ≠ 0)
    (ha : a = k * m.a) (hb : b = k * m.b) (hc : c = k * m.c) : mk_line a b c h = m := by
  obtain ⟨k', hk', ha', hb', hc'⟩ := exists_scale_mk_line a b c h
  refine Line.eq_of_scale (k := k' * k) (mul_ne_zero hk' hk) ?_ ?_ ?_
  · rw [ha', ha]; ring
  · rw [hb', hb]; ring
  · rw [hc', hc]; ring

theorem mk_line_ne_of_c_ne {a b c₁ c₂ : ℝ} (h : a ≠ 0 ∨ b ≠ 0) (hc : c₁ ≠ c₂) :
    mk_line a b c₁ h ≠ mk_line a b c₂ h := by
  intro hEq
  obtain ⟨k, hk, ha1, hb1, hc1⟩ := exists_scale_mk_line a b c₁ h
  obtain ⟨k', hk', ha2, hb2, hc2⟩ := exists_scale_mk_line a b c₂ h
  have hka := congrArg Line.a hEq
  have hkb := congrArg Line.b hEq
  have hkc := congrArg Line.c hEq
  rw [ha1, ha2] at hka
  rw [hb1, hb2] at hkb
  rw [hc1, hc2] at hkc
  have hkk : k = k' := by
    rcases h with h' | h'
    · exact mul_right_cancel₀ h' hka
    · exact mul_right_cancel₀ h' hkb
  rw [hkk] at hkc
  exact hc (mul_left_cancel₀ hk' hkc)

theorem eq_mk_line {l : Line} {a b c : ℝ} (h : a ≠ 0 ∨ b ≠ 0) {k : ℝ} (hk : k ≠ 0)
    (ha : l.a = k * a) (hb : l.b = k * b) (hc : l.c = k * c) : l = mk_line a b c h :=
  (mk_line_eq_of_scale (k := k⁻¹) (inv_ne_zero hk)
    (by rw [ha]; field_simp) (by rw [hb]; field_simp) (by rw [hc]; field_simp)).symm

theorem exists_scale {a b a' b' : ℝ} (h : a ≠ 0 ∨ b ≠ 0) (h' : a' ≠ 0 ∨ b' ≠ 0)
    (hprop : a * b' = b * a') : ∃ k : ℝ, k ≠ 0 ∧ a = k * a' ∧ b = k * b' := by
  have hpos : (0 : ℝ) < a' ^ 2 + b' ^ 2 := by rcases h' with h' | h' <;> positivity
  have hne : a' ^ 2 + b' ^ 2 ≠ 0 := ne_of_gt hpos
  refine ⟨(a * a' + b * b') / (a' ^ 2 + b' ^ 2), ?_, ?_, ?_⟩
  · intro hk0
    rw [div_eq_zero_iff] at hk0
    have hz : a * a' + b * b' = 0 := hk0.resolve_right hne
    rcases h with h | h
    · exact h (by
        have hzz : a * (a' ^ 2 + b' ^ 2) = 0 := by linear_combination a' * hz + b' * hprop
        exact (mul_eq_zero.1 hzz).resolve_right hne)
    · exact h (by
        have hzz : b * (a' ^ 2 + b' ^ 2) = 0 := by linear_combination b' * hz - a' * hprop
        exact (mul_eq_zero.1 hzz).resolve_right hne)
  · rw [div_mul_eq_mul_div, eq_div_iff hne]
    linear_combination b' * hprop
  · rw [div_mul_eq_mul_div, eq_div_iff hne]
    linear_combination (-a') * hprop

theorem exists_on_line (l : Line) : ∃ p : Point, on_line l p := by
  rcases l.normalized with ha | ⟨ha, hb⟩
  · exact ⟨⟨-l.c, 0⟩, by unfold on_line; dsimp only; rw [ha]; ring⟩
  · exact ⟨⟨0, -l.c⟩, by unfold on_line; dsimp only; rw [ha, hb]; ring⟩

theorem exists_line_of_coeffs (a b c : ℝ) (h : a ≠ 0 ∨ b ≠ 0) :
    ∃ l : Line, ∀ p : Point, on_line l p ↔ a * p.x + b * p.y + c = 0 :=
  ⟨mk_line a b c h, on_line_mk_line a b c h⟩

end Origami

theorem Line.eq_of_on_line {l₁ l₂ : Line} (h : ∀ p : Point, on_line l₁ p ↔ on_line l₂ p) :
    l₁ = l₂ := by
  obtain ⟨q, hq⟩ := Origami.exists_on_line l₁
  have hq' : on_line l₁ ⟨q.x - l₁.b, q.y + l₁.a⟩ := by
    unfold on_line at hq ⊢
    dsimp only
    linear_combination hq
  have hA := (h q).1 hq
  have hB := (h _).1 hq'
  unfold on_line at hq hA hB
  dsimp only at hB
  have hprop : l₂.a * l₁.b = l₂.b * l₁.a := by linarith
  obtain ⟨k, hk, hka, hkb⟩ := Origami.exists_scale l₂.nontrivial l₁.nontrivial hprop
  refine (Line.eq_of_scale hk hka hkb ?_).symm
  rw [hka, hkb] at hA
  linear_combination hA - k * hq

theorem Line.eq_iff_on_line {l₁ l₂ : Line} : l₁ = l₂ ↔ ∀ p : Point, on_line l₁ p ↔ on_line l₂ p :=
  ⟨fun h _ => h ▸ Iff.rfl, Line.eq_of_on_line⟩

namespace Origami

theorem f_places_l_nontrivial (f : Fold) (l : Line) :
    l.a * (f.b ^ 2 - f.a ^ 2) - 2 * l.b * f.a * f.b ≠ 0 ∨
      l.b * (f.a ^ 2 - f.b ^ 2) - 2 * l.a * f.a * f.b ≠ 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hA, hB⟩ := hcon
  have key : (l.a * (f.b ^ 2 - f.a ^ 2) - 2 * l.b * f.a * f.b) ^ 2
      + (l.b * (f.a ^ 2 - f.b ^ 2) - 2 * l.a * f.a * f.b) ^ 2
      = (l.a ^ 2 + l.b ^ 2) * (f.a ^ 2 + f.b ^ 2) ^ 2 := by ring
  rw [hA, hB] at key
  have hpos : 0 < (l.a ^ 2 + l.b ^ 2) * (f.a ^ 2 + f.b ^ 2) ^ 2 :=
    mul_pos l.sq_add_sq_pos (pow_pos f.sq_add_sq_pos 2)
  exact absurd (by rw [← key]; ring) (ne_of_gt hpos)

theorem f_places_l_eq_mk_line (f : Fold) (l : Line) :
    f_places_l f l =
      mk_line (l.a * (f.b ^ 2 - f.a ^ 2) - 2 * l.b * f.a * f.b)
        (l.b * (f.a ^ 2 - f.b ^ 2) - 2 * l.a * f.a * f.b)
        (l.c * (f.a ^ 2 + f.b ^ 2) - 2 * f.c * (l.a * f.a + l.b * f.b))
        (f_places_l_nontrivial f l) := by
  have ea : l.a * (f.b * f.b - f.a * f.a) - 2 * l.b * f.a * f.b
      = l.a * (f.b ^ 2 - f.a ^ 2) - 2 * l.b * f.a * f.b := by ring
  have eb : l.b * (f.a * f.a - f.b * f.b) - 2 * l.a * f.a * f.b
      = l.b * (f.a ^ 2 - f.b ^ 2) - 2 * l.a * f.a * f.b := by ring
  have ec : l.c * (f.a * f.a + f.b * f.b) - 2 * f.c * (l.a * f.a + l.b * f.b)
      = l.c * (f.a ^ 2 + f.b ^ 2) - 2 * f.c * (l.a * f.a + l.b * f.b) := by ring
  unfold f_places_l mk_line
  simp only [ea, eb, ec]
  split_ifs with ha <;> rfl

end Origami
