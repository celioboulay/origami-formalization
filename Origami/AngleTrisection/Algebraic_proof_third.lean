import Origami.lightweight_definitions.Structures


abbrev V := EuclideanSpace ℝ (Fin 2)
noncomputable abbrev mkPoint := (EuclideanSpace.equiv (Fin 2) ℝ).symm

noncomputable section
open Set Real
open scoped EuclideanGeometry

def B : V := mkPoint ![0, 0]
def A : V := mkPoint ![0, 2]


theorem test {θ : ℝ} (h : θ ∈ Ioo 0 Real.pi) : 0 < θ := by
  rw [Set.mem_Ioo] at h
  simp [h]
