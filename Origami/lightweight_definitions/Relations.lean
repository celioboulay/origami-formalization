import Origami.lightweight_definitions.Normalisation

namespace Origami

theorem parallel_iff_normals_eq (l₁ l₂ : Line) :
    parallel l₁ l₂ ↔ l₁.a = l₂.a ∧ l₁.b = l₂.b := by
  constructor
  · intro h
    unfold parallel at h
    rcases l₁.normalized with h₁ | ⟨h₁a, h₁b⟩ <;> rcases l₂.normalized with h₂ | ⟨h₂a, h₂b⟩
    · rw [h₁, h₂] at h
      exact ⟨by rw [h₁, h₂], by linarith⟩
    · rw [h₁, h₂a, h₂b] at h; norm_num at h
    · rw [h₁a, h₁b, h₂] at h; norm_num at h
    · exact ⟨by rw [h₁a, h₂a], by rw [h₁b, h₂b]⟩
  · rintro ⟨ha, hb⟩
    unfold parallel
    rw [ha, hb]; ring

theorem perpendicular_comm {l₁ l₂ : Line} : perpendicular l₁ l₂ ↔ perpendicular l₂ l₁ := by
  unfold perpendicular; constructor <;> intro h <;> linarith

theorem parallel_comm {l₁ l₂ : Line} : parallel l₁ l₂ ↔ parallel l₂ l₁ := by
  unfold parallel; constructor <;> intro h <;> linarith

@[simp]
theorem parallel_refl (l : Line) : parallel l l := by unfold parallel; ring

theorem parallel_trans {l₁ l₂ l₃ : Line} (h₁₂ : parallel l₁ l₂) (h₂₃ : parallel l₂ l₃) :
    parallel l₁ l₃ := by
  unfold parallel at *
  have hne := l₂.sq_add_sq_ne_zero
  have key : (l₁.a * l₃.b - l₃.a * l₁.b) * (l₂.a ^ 2 + l₂.b ^ 2) = 0 := by
    linear_combination (l₂.a * l₃.a + l₂.b * l₃.b) * h₁₂ + (l₁.a * l₂.a + l₁.b * l₂.b) * h₂₃
  exact (mul_eq_zero.1 key).resolve_right hne

theorem parallel_of_perpendicular {l m₁ m₂ : Line} (h₁ : perpendicular m₁ l)
    (h₂ : perpendicular m₂ l) : parallel m₁ m₂ := by
  unfold perpendicular at h₁ h₂
  unfold parallel
  have hne := l.sq_add_sq_ne_zero
  have key : (m₁.a * m₂.b - m₂.a * m₁.b) * (l.a ^ 2 + l.b ^ 2) = 0 := by
    linear_combination (m₂.b * l.a - m₂.a * l.b) * h₁ + (m₁.a * l.b - m₁.b * l.a) * h₂
  exact (mul_eq_zero.1 key).resolve_right hne

theorem not_parallel_and_perpendicular {l₁ l₂ : Line} (hpar : parallel l₁ l₂)
    (hperp : perpendicular l₁ l₂) : False := by
  unfold parallel at hpar
  unfold perpendicular at hperp
  have h₁ := l₁.sq_add_sq_pos
  have h₂ := l₂.sq_add_sq_pos
  nlinarith [hpar, hperp, sq_nonneg (l₁.a * l₂.a), sq_nonneg (l₁.b * l₂.b)]

end Origami
