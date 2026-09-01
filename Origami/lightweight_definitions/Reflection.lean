import Origami.lightweight_definitions.Relations

namespace Origami

@[simp]
theorem f_places_p_x (f : Fold) (p : Point) :
    (f_places_p f p).x
      = p.x - 2 * f.a * ((f.a * p.x + f.b * p.y + f.c) / (f.a ^ 2 + f.b ^ 2)) := rfl

@[simp]
theorem f_places_p_y (f : Fold) (p : Point) :
    (f_places_p f p).y
      = p.y - 2 * f.b * ((f.a * p.x + f.b * p.y + f.c) / (f.a ^ 2 + f.b ^ 2)) := rfl

theorem on_line_f_places_p (f : Fold) (l : Line) (p : Point) :
    on_line l (f_places_p f p) ↔
      (f.a ^ 2 + f.b ^ 2) * (l.a * p.x + l.b * p.y + l.c)
        = 2 * (f.a * p.x + f.b * p.y + f.c) * (l.a * f.a + l.b * f.b) := by
  have hN := f.sq_add_sq_ne_zero
  unfold on_line
  simp only [f_places_p_x, f_places_p_y]
  have key : l.a * (p.x - 2 * f.a * ((f.a * p.x + f.b * p.y + f.c) / (f.a ^ 2 + f.b ^ 2)))
      + l.b * (p.y - 2 * f.b * ((f.a * p.x + f.b * p.y + f.c) / (f.a ^ 2 + f.b ^ 2))) + l.c
      = ((f.a ^ 2 + f.b ^ 2) * (l.a * p.x + l.b * p.y + l.c)
          - 2 * (f.a * p.x + f.b * p.y + f.c) * (l.a * f.a + l.b * f.b))
        / (f.a ^ 2 + f.b ^ 2) := by
    field_simp
    ring
  rw [key, div_eq_zero_iff]
  constructor
  · intro hp
    linarith [hp.resolve_right hN]
  · intro hp
    exact Or.inl (by linarith)

theorem f_places_p_mk_line (a b c : ℝ) (h : a ≠ 0 ∨ b ≠ 0) (p : Point) :
    f_places_p (mk_line a b c h) p =
      ⟨p.x - 2 * a * ((a * p.x + b * p.y + c) / (a ^ 2 + b ^ 2)),
       p.y - 2 * b * ((a * p.x + b * p.y + c) / (a ^ 2 + b ^ 2))⟩ := by
  obtain ⟨k, hk, ha, hb, hc⟩ := exists_scale_mk_line a b c h
  have hn : a ^ 2 + b ^ 2 ≠ 0 := by rcases h with h | h <;> positivity
  refine Point.ext ?_ ?_ <;> simp only [f_places_p_x, f_places_p_y, ha, hb, hc] <;> field_simp

theorem on_line_f_places_p_mk_line (a b c : ℝ) (hab : a ≠ 0 ∨ b ≠ 0) (l : Line) (p : Point) :
    on_line l (f_places_p (mk_line a b c hab) p) ↔
      (a ^ 2 + b ^ 2) * (l.a * p.x + l.b * p.y + l.c)
        = 2 * (a * p.x + b * p.y + c) * (l.a * a + l.b * b) := by
  obtain ⟨k, hk, ha, hb, hc⟩ := exists_scale_mk_line a b c hab
  rw [on_line_f_places_p, ha, hb, hc]
  constructor
  · intro hp
    refine mul_left_cancel₀ (pow_ne_zero 2 hk) ?_
    linear_combination hp
  · intro hp
    linear_combination k ^ 2 * hp

theorem f_places_p_involutive (f : Fold) (p : Point) : f_places_p f (f_places_p f p) = p := by
  have hN := f.sq_add_sq_ne_zero
  refine Point.ext ?_ ?_ <;> simp only [f_places_p_x, f_places_p_y] <;> field_simp <;> ring

theorem f_places_p_eq_self_iff (f : Fold) (p : Point) :
    f_places_p f p = p ↔ f_through_p f p := by
  have hN := f.sq_add_sq_ne_zero
  constructor
  · intro hEq
    have hx := congrArg Point.x hEq
    have hy := congrArg Point.y hEq
    simp only [f_places_p_x, f_places_p_y] at hx hy
    have hax : f.a * ((f.a * p.x + f.b * p.y + f.c) / (f.a ^ 2 + f.b ^ 2)) = 0 := by linarith
    have hby : f.b * ((f.a * p.x + f.b * p.y + f.c) / (f.a ^ 2 + f.b ^ 2)) = 0 := by linarith
    have key : (f.a ^ 2 + f.b ^ 2) * ((f.a * p.x + f.b * p.y + f.c) / (f.a ^ 2 + f.b ^ 2)) = 0 := by
      linear_combination f.a * hax + f.b * hby
    rw [mul_div_cancel₀ _ hN] at key
    exact key
  · intro hp
    unfold f_through_p at hp
    refine Point.ext ?_ ?_ <;> simp only [f_places_p_x, f_places_p_y, hp] <;> simp

def dist2 (p q : Point) : ℝ := (p.x - q.x) ^ 2 + (p.y - q.y) ^ 2

theorem dist2_comm (p q : Point) : dist2 p q = dist2 q p := by unfold dist2; ring

@[simp]
theorem dist2_self (p : Point) : dist2 p p = 0 := by unfold dist2; ring

theorem dist2_eq_zero_iff {p q : Point} : dist2 p q = 0 ↔ p = q := by
  unfold dist2
  constructor
  · intro h
    have hx : p.x - q.x = 0 := by nlinarith [sq_nonneg (p.x - q.x), sq_nonneg (p.y - q.y)]
    have hy : p.y - q.y = 0 := by nlinarith [sq_nonneg (p.x - q.x), sq_nonneg (p.y - q.y)]
    exact Point.ext (by linarith) (by linarith)
  · rintro rfl; ring

theorem f_places_p_dist2 (f : Fold) (p q : Point) :
    dist2 (f_places_p f p) (f_places_p f q) = dist2 p q := by
  have hN := f.sq_add_sq_ne_zero
  unfold dist2
  simp only [f_places_p_x, f_places_p_y]
  field_simp
  ring

noncomputable def dist2_line (l : Line) (p : Point) : ℝ :=
  (l.a * p.x + l.b * p.y + l.c) ^ 2 / (l.a ^ 2 + l.b ^ 2)

theorem dist2_line_le_iff (l : Line) (p : Point) (R : ℝ) :
    dist2_line l p ≤ R ↔ (l.a * p.x + l.b * p.y + l.c) ^ 2 ≤ R * (l.a ^ 2 + l.b ^ 2) := by
  rw [dist2_line, div_le_iff₀ l.sq_add_sq_pos]

@[simp]
theorem dist2_line_eq_zero_iff (l : Line) (p : Point) : dist2_line l p = 0 ↔ on_line l p := by
  rw [dist2_line, div_eq_zero_iff]
  constructor
  · intro hp
    exact pow_eq_zero_iff two_ne_zero |>.1 (hp.resolve_right l.sq_add_sq_ne_zero)
  · intro hp
    exact Or.inl (by rw [show l.a * p.x + l.b * p.y + l.c = 0 from hp]; ring)

theorem dist2_line_le_dist2 {l : Line} {p q : Point} (h : on_line l q) :
    dist2_line l p ≤ dist2 p q := by
  unfold on_line at h
  rw [dist2_line_le_iff]
  unfold dist2
  have hE : l.a * p.x + l.b * p.y + l.c = l.a * (p.x - q.x) + l.b * (p.y - q.y) := by linarith
  rw [hE]
  nlinarith [sq_nonneg (l.a * (p.y - q.y) - l.b * (p.x - q.x))]

theorem f_places_l_eq_of_scale {f : Fold} {l m : Line} {k : ℝ} (hk : k ≠ 0)
    (ha : l.a * (f.b ^ 2 - f.a ^ 2) - 2 * l.b * f.a * f.b = k * m.a)
    (hb : l.b * (f.a ^ 2 - f.b ^ 2) - 2 * l.a * f.a * f.b = k * m.b)
    (hc : l.c * (f.a ^ 2 + f.b ^ 2) - 2 * f.c * (l.a * f.a + l.b * f.b) = k * m.c) :
    f_places_l f l = m := by
  rw [f_places_l_eq_mk_line]
  exact mk_line_eq_of_scale hk ha hb hc

theorem on_line_f_places_l_f_places_p (f : Fold) (l : Line) (p : Point) :
    on_line (f_places_l f l) (f_places_p f p) ↔ on_line l p := by
  have hN := f.sq_add_sq_ne_zero
  rw [f_places_l_eq_mk_line, on_line_mk_line]
  simp only [f_places_p_x, f_places_p_y, on_line]
  have key :
      (l.a * (f.b ^ 2 - f.a ^ 2) - 2 * l.b * f.a * f.b) *
          (p.x - 2 * f.a * ((f.a * p.x + f.b * p.y + f.c) / (f.a ^ 2 + f.b ^ 2))) +
        (l.b * (f.a ^ 2 - f.b ^ 2) - 2 * l.a * f.a * f.b) *
          (p.y - 2 * f.b * ((f.a * p.x + f.b * p.y + f.c) / (f.a ^ 2 + f.b ^ 2))) +
        (l.c * (f.a ^ 2 + f.b ^ 2) - 2 * f.c * (l.a * f.a + l.b * f.b))
      = (f.a ^ 2 + f.b ^ 2) * (l.a * p.x + l.b * p.y + l.c) := by
    field_simp
    ring
  rw [key]
  constructor
  · intro h; exact (mul_eq_zero.1 h).resolve_left hN
  · intro h; rw [h, mul_zero]

theorem on_line_f_places_l (f : Fold) (l : Line) (q : Point) :
    on_line (f_places_l f l) q ↔ on_line l (f_places_p f q) := by
  have hq := on_line_f_places_l_f_places_p f l (f_places_p f q)
  rwa [f_places_p_involutive] at hq

theorem perp_places_self {f l : Line} (h : perpendicular f l) : f_places_l f l = l := by
  unfold perpendicular at h
  refine f_places_l_eq_of_scale (k := f.a ^ 2 + f.b ^ 2) f.sq_add_sq_ne_zero ?_ ?_ ?_
  · linear_combination (-2 * f.a) * h
  · linear_combination (-2 * f.b) * h
  · linear_combination (-2 * f.c) * h

theorem f_places_l_self (f : Fold) : f_places_l f f = f := by
  refine f_places_l_eq_of_scale (k := -(f.a ^ 2 + f.b ^ 2)) (neg_ne_zero.2 f.sq_add_sq_ne_zero)
    ?_ ?_ ?_ <;> ring

theorem f_places_l_involutive (f : Fold) (l : Line) : f_places_l f (f_places_l f l) = l := by
  refine Line.eq_of_on_line fun p => ?_
  rw [on_line_f_places_l, on_line_f_places_l, f_places_p_involutive]

end Origami
