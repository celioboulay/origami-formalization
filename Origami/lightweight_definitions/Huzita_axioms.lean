import Origami.lightweight_definitions.Reflection
import Origami.lightweight_definitions.CubicRoot

namespace Origami

theorem fold_through_nontrivial {p₁ p₂ : Point} (h : p₁ ≠ p₂) :
    p₂.y - p₁.y ≠ 0 ∨ p₁.x - p₂.x ≠ 0 := by
  rcases Point.sub_ne_zero_or h with h' | h'
  · exact Or.inr fun hz => h' (by linarith)
  · exact Or.inl h'

noncomputable def fold_through (p₁ p₂ : Point) (h : p₁ ≠ p₂) : Fold :=
  mk_line (p₂.y - p₁.y) (p₁.x - p₂.x) (p₂.x * p₁.y - p₁.x * p₂.y) (fold_through_nontrivial h)

theorem fold_through_left (p₁ p₂ : Point) (h : p₁ ≠ p₂) :
    f_through_p (fold_through p₁ p₂ h) p₁ := by
  rw [fold_through, f_through_p_mk_line]; ring

theorem fold_through_right (p₁ p₂ : Point) (h : p₁ ≠ p₂) :
    f_through_p (fold_through p₁ p₂ h) p₂ := by
  rw [fold_through, f_through_p_mk_line]; ring

theorem huzita_1 (p₁ p₂ : Point) (h : p₁ ≠ p₂) :
    ∃! f : Fold, f_through_p f p₁ ∧ f_through_p f p₂ := by
  refine ⟨fold_through p₁ p₂ h, ⟨fold_through_left p₁ p₂ h, fold_through_right p₁ p₂ h⟩, ?_⟩
  · rintro g ⟨hg₁, hg₂⟩
    unfold f_through_p at hg₁ hg₂
    rw [fold_through]
    have hnt := fold_through_nontrivial h
    have hdir : g.a * (p₁.x - p₂.x) = g.b * (p₂.y - p₁.y) := by linear_combination hg₁ - hg₂
    obtain ⟨k, hk, hka, hkb⟩ := exists_scale g.nontrivial hnt hdir
    exact eq_mk_line _ hk hka hkb (by linear_combination hg₁ - p₁.x * hka - p₁.y * hkb)

noncomputable def fold_bisector (p₁ p₂ : Point) (h : p₁ ≠ p₂) : Fold :=
  mk_line (p₂.x - p₁.x) (p₂.y - p₁.y) ((p₁.x ^ 2 + p₁.y ^ 2 - p₂.x ^ 2 - p₂.y ^ 2) / 2)
    (Point.sub_ne_zero_or h)

theorem fold_bisector_places (p₁ p₂ : Point) (h : p₁ ≠ p₂) :
    f_places_p (fold_bisector p₁ p₂ h) p₁ = p₂ := by
  have hn := Point.sub_sq_add_sq_ne_zero h
  rw [fold_bisector, f_places_p_mk_line]
  refine Point.ext ?_ ?_ <;> dsimp only <;> field_simp <;> ring

theorem fold_bisector_through (p₁ p₂ q : Point) (h : p₁ ≠ p₂) :
    f_through_p (fold_bisector p₁ p₂ h) q ↔ dist2 q p₁ = dist2 q p₂ := by
  rw [fold_bisector, f_through_p_mk_line]
  unfold dist2
  constructor
  · intro hh; linear_combination 2 * hh
  · intro hh; linear_combination (1 / 2) * hh

theorem huzita_2 (p₁ p₂ : Point) (h : p₁ ≠ p₂) :
    ∃! f : Fold, f_places_p f p₁ = p₂ := by
  have hnt := Point.sub_ne_zero_or h
  refine ⟨fold_bisector p₁ p₂ h, fold_bisector_places p₁ p₂ h, ?_⟩
  · rintro g hg
    rw [fold_bisector]
    have hNg := g.sq_add_sq_ne_zero
    have hx := congrArg Point.x hg
    have hy := congrArg Point.y hg
    simp only [f_places_p_x, f_places_p_y] at hx hy
    have hdir : g.a * (p₂.y - p₁.y) = g.b * (p₂.x - p₁.x) := by
      have hx' : p₂.x - p₁.x
          = -(2 * g.a * ((g.a * p₁.x + g.b * p₁.y + g.c) / (g.a ^ 2 + g.b ^ 2))) := by linarith
      have hy' : p₂.y - p₁.y
          = -(2 * g.b * ((g.a * p₁.x + g.b * p₁.y + g.c) / (g.a ^ 2 + g.b ^ 2))) := by linarith
      rw [hx', hy']; ring
    obtain ⟨k, hk, hka, hkb⟩ := exists_scale g.nontrivial hnt hdir
    have hmid : g.a * (p₁.x + p₂.x) + g.b * (p₁.y + p₂.y) + 2 * g.c = 0 := by
      rw [← hx, ← hy]; field_simp; ring
    refine eq_mk_line _ hk hka hkb ?_
    linear_combination (1 / 2) * hmid - ((p₁.x + p₂.x) / 2) * hka - ((p₁.y + p₂.y) / 2) * hkb

theorem bisector_places_line {l₁ l₂ : Line} {t s : ℝ}
    (ht : t ^ 2 = l₁.a ^ 2 + l₁.b ^ 2) (hs : s ^ 2 = l₂.a ^ 2 + l₂.b ^ 2)
    (hnt : s * l₁.a + t * l₂.a ≠ 0 ∨ s * l₁.b + t * l₂.b ≠ 0) :
    f_places_l (mk_line (s * l₁.a + t * l₂.a) (s * l₁.b + t * l₂.b) (s * l₁.c + t * l₂.c) hnt) l₁
      = l₂ := by
  have hμ : l₁.a * l₂.a + l₁.b * l₂.b + t * s ≠ 0 := by
    intro h0
    have key : (s * l₁.a + t * l₂.a) ^ 2 + (s * l₁.b + t * l₂.b) ^ 2
        = 2 * t * s * (l₁.a * l₂.a + l₁.b * l₂.b + t * s) := by
      linear_combination ((l₁.a ^ 2 + l₁.b ^ 2) - 2 * t ^ 2) * hs - (l₂.a ^ 2 + l₂.b ^ 2) * ht
    rw [h0, mul_zero] at key
    rcases hnt with h' | h' <;>
      exact h' (by nlinarith [sq_nonneg (s * l₁.a + t * l₂.a), sq_nonneg (s * l₁.b + t * l₂.b)])
  obtain ⟨κ, hκ, hA, hB, hC⟩ := exists_scale_mk_line _ _ _ hnt
  refine f_places_l_eq_of_scale
    (k := κ ^ 2 * (-2 * (l₁.a ^ 2 + l₁.b ^ 2) * (l₁.a * l₂.a + l₁.b * l₂.b + t * s)))
    (by
      refine mul_ne_zero (pow_ne_zero 2 hκ) (mul_ne_zero ?_ hμ)
      simpa using mul_ne_zero (two_ne_zero) l₁.sq_add_sq_ne_zero)
    ?_ ?_ ?_
  · rw [hA, hB]
    linear_combination
      (κ ^ 2 * (l₁.a * l₂.b ^ 2 - l₁.a * l₂.a ^ 2 - 2 * l₂.a * l₁.b * l₂.b)) * ht
      - (κ ^ 2 * l₁.a * (l₁.a ^ 2 + l₁.b ^ 2)) * hs
  · rw [hA, hB]
    linear_combination
      (κ ^ 2 * (l₁.b * l₂.a ^ 2 - l₁.b * l₂.b ^ 2 - 2 * l₁.a * l₂.a * l₂.b)) * ht
      - (κ ^ 2 * l₁.b * (l₁.a ^ 2 + l₁.b ^ 2)) * hs
  · rw [hA, hB, hC]
    linear_combination
      (κ ^ 2 * (l₁.c * (l₂.a ^ 2 + l₂.b ^ 2)
        - 2 * l₂.c * (l₁.a * l₂.a + l₁.b * l₂.b))) * ht
      - (κ ^ 2 * l₁.c * (l₁.a ^ 2 + l₁.b ^ 2)) * hs

theorem bisector_nontrivial {l₁ l₂ : Line} {t s : ℝ}
    (ht : t ^ 2 = l₁.a ^ 2 + l₁.b ^ 2) (hs : s ^ 2 = l₂.a ^ 2 + l₂.b ^ 2)
    (hμ : l₁.a * l₂.a + l₁.b * l₂.b + t * s ≠ 0) :
    s * l₁.a + t * l₂.a ≠ 0 ∨ s * l₁.b + t * l₂.b ≠ 0 := by
  have ht0 : t ≠ 0 := fun h0 => l₁.sq_add_sq_ne_zero (by rw [← ht, h0]; ring)
  have hs0 : s ≠ 0 := fun h0 => l₂.sq_add_sq_ne_zero (by rw [← hs, h0]; ring)
  by_contra hcon
  push Not at hcon
  obtain ⟨hA, hB⟩ := hcon
  have key : (s * l₁.a + t * l₂.a) ^ 2 + (s * l₁.b + t * l₂.b) ^ 2
      = 2 * t * s * (l₁.a * l₂.a + l₁.b * l₂.b + t * s) := by
    linear_combination ((l₁.a ^ 2 + l₁.b ^ 2) - 2 * t ^ 2) * hs - (l₂.a ^ 2 + l₂.b ^ 2) * ht
  rw [hA, hB] at key
  have hz : (2 : ℝ) * t * s * (l₁.a * l₂.a + l₁.b * l₂.b + t * s) = 0 := by linarith [key]
  rcases mul_eq_zero.1 hz with h' | h'
  · rcases mul_eq_zero.1 h' with h'' | h''
    · rcases mul_eq_zero.1 h'' with h''' | h''' <;> [exact two_ne_zero h'''; exact ht0 h''']
    · exact hs0 h''
  · exact hμ h'

theorem exists_bisector {l₁ l₂ : Line} {t s : ℝ}
    (ht : t ^ 2 = l₁.a ^ 2 + l₁.b ^ 2) (hs : s ^ 2 = l₂.a ^ 2 + l₂.b ^ 2)
    (hμ : l₁.a * l₂.a + l₁.b * l₂.b + t * s ≠ 0) :
    ∃ f : Fold, f_places_l f l₁ = l₂ :=
  ⟨_, bisector_places_line ht hs (bisector_nontrivial ht hs hμ)⟩

theorem inner_add_norms_pos (l₁ l₂ : Line) :
    0 < l₁.a * l₂.a + l₁.b * l₂.b
      + Real.sqrt (l₁.a ^ 2 + l₁.b ^ 2) * Real.sqrt (l₂.a ^ 2 + l₂.b ^ 2) := by
  have h₁ := l₁.sq_add_sq_pos
  have h₂ := l₂.sq_add_sq_pos
  have hs₁ : Real.sqrt (l₁.a ^ 2 + l₁.b ^ 2) ^ 2 = l₁.a ^ 2 + l₁.b ^ 2 := Real.sq_sqrt h₁.le
  have hs₂ : Real.sqrt (l₂.a ^ 2 + l₂.b ^ 2) ^ 2 = l₂.a ^ 2 + l₂.b ^ 2 := Real.sq_sqrt h₂.le
  have hp : 0 < Real.sqrt (l₁.a ^ 2 + l₁.b ^ 2) * Real.sqrt (l₂.a ^ 2 + l₂.b ^ 2) :=
    mul_pos (Real.sqrt_pos.2 h₁) (Real.sqrt_pos.2 h₂)
  by_cases hpar : parallel l₁ l₂
  · obtain ⟨ha, hb⟩ := (parallel_iff_normals_eq l₁ l₂).1 hpar
    rw [← ha, ← hb]
    nlinarith [h₁, hp]
  · have hcross : l₁.a * l₂.b - l₂.a * l₁.b ≠ 0 := fun hz => hpar hz
    have hsq : 0 < (l₁.a * l₂.b - l₂.a * l₁.b) ^ 2 := by positivity
    have key : (Real.sqrt (l₁.a ^ 2 + l₁.b ^ 2) * Real.sqrt (l₂.a ^ 2 + l₂.b ^ 2)) ^ 2
        = (l₁.a * l₂.a + l₁.b * l₂.b) ^ 2 + (l₁.a * l₂.b - l₂.a * l₁.b) ^ 2 := by
      rw [mul_pow, hs₁, hs₂]; ring
    nlinarith [key, hsq, hp]

noncomputable def fold_bisect_lines (l₁ l₂ : Line) : Fold :=
  mk_line
    (Real.sqrt (l₂.a ^ 2 + l₂.b ^ 2) * l₁.a + Real.sqrt (l₁.a ^ 2 + l₁.b ^ 2) * l₂.a)
    (Real.sqrt (l₂.a ^ 2 + l₂.b ^ 2) * l₁.b + Real.sqrt (l₁.a ^ 2 + l₁.b ^ 2) * l₂.b)
    (Real.sqrt (l₂.a ^ 2 + l₂.b ^ 2) * l₁.c + Real.sqrt (l₁.a ^ 2 + l₁.b ^ 2) * l₂.c)
    (bisector_nontrivial (Real.sq_sqrt l₁.sq_add_sq_pos.le) (Real.sq_sqrt l₂.sq_add_sq_pos.le)
      (inner_add_norms_pos l₁ l₂).ne')

theorem fold_bisect_lines_places (l₁ l₂ : Line) :
    f_places_l (fold_bisect_lines l₁ l₂) l₁ = l₂ := by
  rw [fold_bisect_lines]
  exact bisector_places_line (Real.sq_sqrt l₁.sq_add_sq_pos.le)
    (Real.sq_sqrt l₂.sq_add_sq_pos.le) _

theorem huzita_3 (l₁ l₂ : Line) : ∃ f : Fold, f_places_l f l₁ = l₂ :=
  ⟨fold_bisect_lines l₁ l₂, fold_bisect_lines_places l₁ l₂⟩

noncomputable def fold_perp (p : Point) (l : Line) : Fold :=
  mk_line (-l.b) l.a (l.b * p.x - l.a * p.y) (Line.perp_nontrivial l)

theorem fold_perp_through (p : Point) (l : Line) : f_through_p (fold_perp p l) p := by
  rw [fold_perp, f_through_p_mk_line]; ring

theorem fold_perp_perpendicular (p : Point) (l : Line) : perpendicular (fold_perp p l) l := by
  obtain ⟨k, hk, hka, hkb, _⟩ :=
    exists_scale_mk_line (-l.b) l.a (l.b * p.x - l.a * p.y) (Line.perp_nontrivial l)
  unfold perpendicular fold_perp
  rw [hka, hkb]; ring

theorem huzita_4 (p : Point) (l : Line) :
    ∃! f : Fold, perpendicular f l ∧ f_through_p f p := by
  have hnt := Line.perp_nontrivial l
  refine ⟨fold_perp p l, ⟨fold_perp_perpendicular p l, fold_perp_through p l⟩, ?_⟩
  · rintro g ⟨hperp, hthrough⟩
    unfold perpendicular at hperp
    unfold f_through_p at hthrough
    rw [fold_perp]
    have hdir : g.a * l.a = g.b * -l.b := by linarith
    obtain ⟨k, hk, hka, hkb⟩ := exists_scale g.nontrivial hnt hdir
    exact eq_mk_line _ hk hka hkb (by linear_combination hthrough - p.x * hka - p.y * hkb)

theorem exists_on_line_dist2 (p₂ : Point) (l₁ : Line) (R : ℝ) (h : dist2_line l₁ p₂ ≤ R) :
    ∃ q : Point, on_line l₁ q ∧ dist2 p₂ q = R := by
  rw [dist2_line_le_iff] at h
  have hN : l₁.a ^ 2 + l₁.b ^ 2 ≠ 0 := l₁.sq_add_sq_ne_zero
  obtain ⟨S, hS⟩ : ∃ S : ℝ, S ^ 2
      = R * (l₁.a ^ 2 + l₁.b ^ 2) - (l₁.a * p₂.x + l₁.b * p₂.y + l₁.c) ^ 2 :=
    ⟨Real.sqrt _, Real.sq_sqrt (by linarith)⟩
  refine ⟨⟨p₂.x - ((l₁.a * p₂.x + l₁.b * p₂.y + l₁.c) * l₁.a + S * l₁.b) / (l₁.a ^ 2 + l₁.b ^ 2),
      p₂.y + (S * l₁.a - (l₁.a * p₂.x + l₁.b * p₂.y + l₁.c) * l₁.b) / (l₁.a ^ 2 + l₁.b ^ 2)⟩,
    ?_, ?_⟩
  · unfold on_line
    dsimp only
    field_simp
    ring
  · unfold dist2
    dsimp only
    field_simp
    linear_combination (l₁.a ^ 2 + l₁.b ^ 2) * hS

theorem huzita_5 (p₁ p₂ : Point) (l₁ : Line) (h : dist2_line l₁ p₂ ≤ dist2 p₁ p₂) :
    ∃ f : Fold, f_through_p f p₂ ∧ on_line l₁ (f_places_p f p₁) := by
  obtain ⟨q, hqon, hqdist⟩ := exists_on_line_dist2 p₂ l₁ (dist2 p₁ p₂) h
  by_cases hpq : p₁ = q
  · have hp₁ : on_line l₁ p₁ := by rw [hpq]; exact hqon
    by_cases hp : p₁ = p₂
    · refine ⟨fold_perp p₁ l₁, ?_, ?_⟩
      · rw [← hp]
        exact fold_perp_through p₁ l₁
      · rw [(f_places_p_eq_self_iff _ _).2 (fold_perp_through p₁ l₁)]
        exact hp₁
    · refine ⟨fold_through p₁ p₂ hp, ?_, ?_⟩
      · exact fold_through_right p₁ p₂ hp
      · rw [(f_places_p_eq_self_iff _ _).2 (fold_through_left p₁ p₂ hp)]
        exact hp₁
  · refine ⟨fold_bisector p₁ q hpq, ?_, ?_⟩
    · rw [fold_bisector_through, hqdist]
      exact dist2_comm p₂ p₁
    · rw [fold_bisector_places]
      exact hqon

theorem exists_fold_normal (l₁ l₂ : Line) (D₁ D₂ δx δy : ℝ) :
    ∃ a b : ℝ, (a ≠ 0 ∨ b ≠ 0) ∧
      (a ^ 2 + b ^ 2) * ((l₁.a * a + l₁.b * b) * D₂ - (l₂.a * a + l₂.b * b) * D₁)
        - 2 * (l₁.a * a + l₁.b * b) * (l₂.a * a + l₂.b * b) * (a * δx + b * δy) = 0 := by
  obtain ⟨a, b, hab, hroot⟩ := exists_hom_cubic_root
    (l₁.a * D₂ - l₂.a * D₁ - 2 * l₁.a * l₂.a * δx)
    (l₁.b * D₂ - l₂.b * D₁ - 2 * (l₁.a * l₂.a * δy + (l₁.a * l₂.b + l₁.b * l₂.a) * δx))
    (l₁.a * D₂ - l₂.a * D₁ - 2 * ((l₁.a * l₂.b + l₁.b * l₂.a) * δy + l₁.b * l₂.b * δx))
    (l₁.b * D₂ - l₂.b * D₁ - 2 * l₁.b * l₂.b * δy)
  exact ⟨a, b, hab, by linear_combination hroot⟩

theorem huzita_6_aux (p₁ p₂ : Point) (l₁ l₂ : Line) (h : ¬ parallel l₁ l₂)
    (hD₁ : ¬ on_line l₁ p₁) :
    ∃ f : Fold, on_line l₁ (f_places_p f p₁) ∧ on_line l₂ (f_places_p f p₂) := by
  unfold on_line at hD₁
  obtain ⟨a, b, hab, hP⟩ := exists_fold_normal l₁ l₂
    (l₁.a * p₁.x + l₁.b * p₁.y + l₁.c) (l₂.a * p₂.x + l₂.b * p₂.y + l₂.c)
    (p₂.x - p₁.x) (p₂.y - p₁.y)
  have hN : a ^ 2 + b ^ 2 ≠ 0 := by rcases hab with h' | h' <;> positivity
  have hL₁ : l₁.a * a + l₁.b * b ≠ 0 := by
    intro h0
    rw [h0] at hP
    have key : (a ^ 2 + b ^ 2)
        * ((l₂.a * a + l₂.b * b) * (l₁.a * p₁.x + l₁.b * p₁.y + l₁.c)) = 0 := by
      linear_combination -hP
    have hL₂ : l₂.a * a + l₂.b * b = 0 :=
      (mul_eq_zero.1 ((mul_eq_zero.1 key).resolve_left hN)).resolve_right hD₁
    have hpar : (l₁.a * l₂.b - l₂.a * l₁.b) * (a ^ 2 + b ^ 2) = 0 := by
      linear_combination (a * l₂.b - b * l₂.a) * h0 + (b * l₁.a - a * l₁.b) * hL₂
    unfold parallel at h
    exact h ((mul_eq_zero.1 hpar).resolve_right hN)
  have h2L₁ : 2 * (l₁.a * a + l₁.b * b) ≠ 0 := mul_ne_zero two_ne_zero hL₁
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c =
      ((a ^ 2 + b ^ 2) * (l₁.a * p₁.x + l₁.b * p₁.y + l₁.c)
          - 2 * (l₁.a * a + l₁.b * b) * (a * p₁.x + b * p₁.y))
        / (2 * (l₁.a * a + l₁.b * b)) := ⟨_, rfl⟩
  have hc : 2 * (l₁.a * a + l₁.b * b) * c
      = (a ^ 2 + b ^ 2) * (l₁.a * p₁.x + l₁.b * p₁.y + l₁.c)
        - 2 * (l₁.a * a + l₁.b * b) * (a * p₁.x + b * p₁.y) := by
    rw [hcdef]; field_simp
  have g₁ : on_line l₁ (f_places_p (mk_line a b c hab) p₁) := by
    rw [on_line_f_places_p_mk_line]
    linear_combination -hc
  have g₂ : on_line l₂ (f_places_p (mk_line a b c hab) p₂) := by
    rw [on_line_f_places_p_mk_line]
    refine mul_left_cancel₀ hL₁ ?_
    linear_combination hP - (l₂.a * a + l₂.b * b) * hc
  exact ⟨mk_line a b c hab, g₁, g₂⟩

theorem huzita_6 (p₁ p₂ : Point) (l₁ l₂ : Line) (h : ¬ parallel l₁ l₂) :
    ∃ f : Fold, on_line l₁ (f_places_p f p₁) ∧ on_line l₂ (f_places_p f p₂) := by
  by_cases hD₁ : on_line l₁ p₁
  case neg => exact huzita_6_aux p₁ p₂ l₁ l₂ h hD₁
  by_cases hD₂ : on_line l₂ p₂
  case neg =>
    obtain ⟨f, h₁, h₂⟩ := huzita_6_aux p₂ p₁ l₂ l₁ (fun hp => h (parallel_comm.1 hp)) hD₂
    exact ⟨f, h₂, h₁⟩
  by_cases hp : p₁ = p₂
  · have hfix₁ : f_places_p (fold_perp p₁ l₁) p₁ = p₁ :=
      (f_places_p_eq_self_iff _ _).2 (fold_perp_through p₁ l₁)
    have hfix₂ : f_places_p (fold_perp p₁ l₁) p₂ = p₂ := by rw [← hp]; exact hfix₁
    have g₁ : on_line l₁ (f_places_p (fold_perp p₁ l₁) p₁) := by rw [hfix₁]; exact hD₁
    have g₂ : on_line l₂ (f_places_p (fold_perp p₁ l₁) p₂) := by rw [hfix₂]; exact hD₂
    exact ⟨fold_perp p₁ l₁, g₁, g₂⟩
  · have hfix₁ : f_places_p (fold_through p₁ p₂ hp) p₁ = p₁ :=
      (f_places_p_eq_self_iff _ _).2 (fold_through_left p₁ p₂ hp)
    have hfix₂ : f_places_p (fold_through p₁ p₂ hp) p₂ = p₂ :=
      (f_places_p_eq_self_iff _ _).2 (fold_through_right p₁ p₂ hp)
    have g₁ : on_line l₁ (f_places_p (fold_through p₁ p₂ hp) p₁) := by rw [hfix₁]; exact hD₁
    have g₂ : on_line l₂ (f_places_p (fold_through p₁ p₂ hp) p₂) := by rw [hfix₂]; exact hD₂
    exact ⟨fold_through p₁ p₂ hp, g₁, g₂⟩

theorem cross_ne_zero {l₁ l₂ : Line} (h : ¬ parallel l₁ l₂) : l₁.b * l₂.a - l₁.a * l₂.b ≠ 0 :=
  fun hz => h (by unfold parallel; linarith)

theorem fold_perp_place_nontrivial {l₁ l₂ : Line} (h : ¬ parallel l₁ l₂) :
    2 * (l₁.b * l₂.a - l₁.a * l₂.b) * -l₂.b ≠ 0 ∨
      2 * (l₁.b * l₂.a - l₁.a * l₂.b) * l₂.a ≠ 0 := by
  have h2D := mul_ne_zero (two_ne_zero (α := ℝ)) (cross_ne_zero h)
  rcases Line.perp_nontrivial l₂ with h' | h'
  · exact Or.inl (mul_ne_zero h2D h')
  · exact Or.inr (mul_ne_zero h2D h')

noncomputable def fold_perp_place (p : Point) (l₁ l₂ : Line) (h : ¬ parallel l₁ l₂) : Fold :=
  mk_line
    (2 * (l₁.b * l₂.a - l₁.a * l₂.b) * -l₂.b)
    (2 * (l₁.b * l₂.a - l₁.a * l₂.b) * l₂.a)
    ((l₁.a * p.x + l₁.b * p.y + l₁.c) * (l₂.a ^ 2 + l₂.b ^ 2)
      - 2 * (l₁.b * l₂.a - l₁.a * l₂.b) * (-l₂.b * p.x + l₂.a * p.y))
    (fold_perp_place_nontrivial h)

theorem fold_perp_place_places (p : Point) (l₁ l₂ : Line) (h : ¬ parallel l₁ l₂) :
    on_line l₁ (f_places_p (fold_perp_place p l₁ l₂ h) p) := by
  rw [fold_perp_place, on_line_f_places_p_mk_line]; ring

theorem fold_perp_place_perpendicular (p : Point) (l₁ l₂ : Line) (h : ¬ parallel l₁ l₂) :
    perpendicular (fold_perp_place p l₁ l₂ h) l₂ := by
  obtain ⟨k, hk, hka, hkb, _⟩ := exists_scale_mk_line _ _ _ (fold_perp_place_nontrivial h)
  unfold perpendicular fold_perp_place
  rw [hka, hkb]; ring

theorem huzita_7 (p : Point) (l₁ l₂ : Line) (h : ¬ parallel l₁ l₂) :
    ∃! f : Fold, on_line l₁ (f_places_p f p) ∧ perpendicular f l₂ := by
  have hD := cross_ne_zero h
  have h2D : (2 : ℝ) * (l₁.b * l₂.a - l₁.a * l₂.b) ≠ 0 := mul_ne_zero two_ne_zero hD
  have hnt := Line.perp_nontrivial l₂
  refine ⟨fold_perp_place p l₁ l₂ h,
    ⟨fold_perp_place_places p l₁ l₂ h, fold_perp_place_perpendicular p l₁ l₂ h⟩, ?_⟩
  · rintro g ⟨hinc, hperp⟩
    unfold perpendicular at hperp
    rw [on_line_f_places_p] at hinc
    rw [fold_perp_place]
    have hdir : g.a * l₂.a = g.b * -l₂.b := by linarith
    obtain ⟨k, hk, hka, hkb⟩ := exists_scale g.nontrivial hnt hdir
    have hkey : 2 * (l₁.b * l₂.a - l₁.a * l₂.b) * (g.a * p.x + g.b * p.y + g.c)
        = k * (l₂.a ^ 2 + l₂.b ^ 2) * (l₁.a * p.x + l₁.b * p.y + l₁.c) := by
      rw [hka, hkb] at hinc ⊢
      refine mul_left_cancel₀ hk ?_
      linear_combination -hinc
    refine eq_mk_line _ (k := k / (2 * (l₁.b * l₂.a - l₁.a * l₂.b))) (div_ne_zero hk h2D)
      ?_ ?_ ?_
    · rw [hka, div_mul_eq_mul_div, eq_div_iff h2D]; ring
    · rw [hkb, div_mul_eq_mul_div, eq_div_iff h2D]; ring
    · rw [div_mul_eq_mul_div, eq_div_iff h2D]
      rw [hka, hkb] at hkey
      linear_combination hkey

theorem eq_fold_through_iff (p₁ p₂ : Point) (h : p₁ ≠ p₂) (f : Fold) :
    f = fold_through p₁ p₂ h ↔ f_through_p f p₁ ∧ f_through_p f p₂ := by
  have hw : f_through_p (fold_through p₁ p₂ h) p₁ ∧ f_through_p (fold_through p₁ p₂ h) p₂ :=
    ⟨fold_through_left p₁ p₂ h, fold_through_right p₁ p₂ h⟩
  exact ⟨fun hf => by rw [hf]; exact hw, fun hf => (huzita_1 p₁ p₂ h).unique hf hw⟩

theorem eq_fold_bisector_iff (p₁ p₂ : Point) (h : p₁ ≠ p₂) (f : Fold) :
    f = fold_bisector p₁ p₂ h ↔ f_places_p f p₁ = p₂ :=
  ⟨fun hf => by rw [hf]; exact fold_bisector_places p₁ p₂ h,
    fun hf => (huzita_2 p₁ p₂ h).unique hf (fold_bisector_places p₁ p₂ h)⟩

theorem eq_fold_perp_iff (p : Point) (l : Line) (f : Fold) :
    f = fold_perp p l ↔ perpendicular f l ∧ f_through_p f p := by
  have hw : perpendicular (fold_perp p l) l ∧ f_through_p (fold_perp p l) p :=
    ⟨fold_perp_perpendicular p l, fold_perp_through p l⟩
  exact ⟨fun hf => by rw [hf]; exact hw, fun hf => (huzita_4 p l).unique hf hw⟩

theorem eq_fold_perp_place_iff (p : Point) (l₁ l₂ : Line) (h : ¬ parallel l₁ l₂) (f : Fold) :
    f = fold_perp_place p l₁ l₂ h ↔ on_line l₁ (f_places_p f p) ∧ perpendicular f l₂ := by
  have hw : on_line l₁ (f_places_p (fold_perp_place p l₁ l₂ h) p) ∧
      perpendicular (fold_perp_place p l₁ l₂ h) l₂ :=
    ⟨fold_perp_place_places p l₁ l₂ h, fold_perp_place_perpendicular p l₁ l₂ h⟩
  exact ⟨fun hf => by rw [hf]; exact hw, fun hf => (huzita_7 p l₁ l₂ h).unique hf hw⟩

end Origami
