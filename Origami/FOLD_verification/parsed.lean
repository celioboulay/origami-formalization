import Origami.FOLD_verification.crease_pattern_verif
set_option linter.style.emptyLine false

def A : Point := ⟨0, 0⟩
def B : Point := ⟨1, 0⟩
def C : Point := ⟨1, 1⟩
def D : Point := ⟨0, 1⟩
def E : Point := ⟨0.5, 0.5⟩

def AE : Ray := ⟨A, E, Label.M⟩
def BE : Ray := ⟨B, E, Label.M⟩
def CE : Ray := ⟨C, E, Label.M⟩
def DE : Ray := ⟨D, E, Label.V⟩

def P : CreasePattern := {
  γ := {E},
  V := {A, B, C, D},
  E := {AE, BE, CE, DE}
}

theorem P1_m : Maekawa_condition P := by
  unfold Maekawa_condition;
  intro v hv M n_M V n_V
  replace hv : v = E := hv; subst hv

  have hM : M = {AE, BE, CE} := by
    ext e; unfold M P AE BE CE DE; simp; grind;


  have hV : V = {DE} := by
    ext e; unfold V P AE BE CE DE; simp; grind;


  have hnM : n_M = 3 := by
    unfold n_M; rw [hM];
    unfold AE BE CE A B C E; simp;

  have hnV : n_V = 1 := by
    unfold n_V; rw [hV];
    unfold DE E D; simp;

  simp [hnM, hnV];
