import Mathlib

namespace Origami

private theorem exists_cubic_root_pos {A B C D : ℝ} (hA : 0 < A) :
    ∃ t : ℝ, A * t ^ 3 + B * t ^ 2 + C * t + D = 0 := by
  set M : ℝ := (|B| + |C| + |D|) / A + 1 with hMdef
  have hM1 : 1 ≤ M := by
    have : 0 ≤ (|B| + |C| + |D|) / A := div_nonneg (by positivity) hA.le
    simp only [hMdef]; linarith
  have hMpos : 0 < M := by linarith
  have hMM : 0 ≤ M ^ 2 - M := by nlinarith
  have hM21 : 0 ≤ M ^ 2 - 1 := by nlinarith
  have hAM2 : 0 < A * M ^ 2 := mul_pos hA (pow_pos hMpos 2)
  have hAM : A * M = |B| + |C| + |D| + A := by simp only [hMdef]; field_simp
  have e2 : A * M ^ 3 - (|B| + |C| + |D|) * M ^ 2 = A * M ^ 2 := by
    linear_combination M ^ 2 * hAM
  have hCM : 0 ≤ |C| * (M ^ 2 - M) := mul_nonneg (abs_nonneg C) hMM
  have hDM : 0 ≤ |D| * (M ^ 2 - 1) := mul_nonneg (abs_nonneg D) hM21
  have hup : 0 < A * M ^ 3 + B * M ^ 2 + C * M + D := by
    have hB : 0 ≤ (B + |B|) * M ^ 2 := mul_nonneg (by linarith [neg_abs_le B]) (sq_nonneg M)
    have hC : 0 ≤ (C + |C|) * M := mul_nonneg (by linarith [neg_abs_le C]) hMpos.le
    have hD : 0 ≤ D + |D| := by linarith [neg_abs_le D]
    nlinarith [e2, hB, hC, hD, hCM, hDM, hAM2]
  have hdown : A * (-M) ^ 3 + B * (-M) ^ 2 + C * (-M) + D < 0 := by
    have hB : 0 ≤ (|B| - B) * M ^ 2 := mul_nonneg (by linarith [le_abs_self B]) (sq_nonneg M)
    have hC : 0 ≤ (|C| + C) * M := mul_nonneg (by linarith [neg_le_abs C]) hMpos.le
    have hD : 0 ≤ |D| - D := by linarith [le_abs_self D]
    nlinarith [e2, hB, hC, hD, hCM, hDM, hAM2]
  have hcont : ContinuousOn (fun t : ℝ => A * t ^ 3 + B * t ^ 2 + C * t + D)
      (Set.Icc (-M) M) := by fun_prop
  have hle : -M ≤ M := by linarith
  obtain ⟨t, -, ht⟩ := intermediate_value_Icc hle hcont ⟨hdown.le, hup.le⟩
  exact ⟨t, ht⟩

theorem exists_cubic_root {A B C D : ℝ} (hA : A ≠ 0) :
    ∃ t : ℝ, A * t ^ 3 + B * t ^ 2 + C * t + D = 0 := by
  rcases lt_or_gt_of_ne hA with hneg | hpos
  · obtain ⟨t, ht⟩ := exists_cubic_root_pos (A := -A) (B := -B) (C := -C) (D := -D) (by linarith)
    exact ⟨t, by linarith⟩
  · exact exists_cubic_root_pos hpos

theorem exists_hom_cubic_root (A B C E : ℝ) :
    ∃ a b : ℝ, (a ≠ 0 ∨ b ≠ 0) ∧ A * a ^ 3 + B * a ^ 2 * b + C * a * b ^ 2 + E * b ^ 3 = 0 := by
  by_cases hA : A = 0
  · exact ⟨1, 0, Or.inl one_ne_zero, by simp [hA]⟩
  · obtain ⟨t, ht⟩ := exists_cubic_root (A := A) (B := B) (C := C) (D := E) hA
    exact ⟨t, 1, Or.inr one_ne_zero, by linear_combination ht⟩

end Origami
