import Origami.FOLD_verification.crease_pattern_verif

set_option linter.style.emptyLine false

def A : Point := ⟨0, 0⟩
def B : Point := ⟨1, 0⟩
def C : Point := ⟨1, 1⟩
def D : Point := ⟨0, 1⟩
def X : Vertex := ⟨0.5, 0.5⟩

def DX : Ray := ⟨D, X, Label.V⟩
def XB : Ray := ⟨X, B, Label.V⟩



def P1 : CreasePattern := {
  γ := {X},
  V := {A, B, C, D}
  E := {DX, XB}
}


theorem P1_m : Maekawa_condition P1 := by
  unfold Maekawa_condition;

  intro v hv M n_M V n_V
  replace hv : v = X := hv; subst hv

  have hM : M = ∅ := by
    ext e; unfold M P1 DX XB; grind

  have hV : V = {DX, XB} := by
    ext e; unfold V P1 DX XB; grind;

  have h_ne : DX ≠ XB := by
    simp [DX, XB, D, B]; grind;

  have hnM : n_M = 0 := by
    unfold n_M; rw [hM]; simp
  have hnV : n_V = 2 := by
    unfold n_V; simp [hV, h_ne]

  simp [hnM, hnV];
