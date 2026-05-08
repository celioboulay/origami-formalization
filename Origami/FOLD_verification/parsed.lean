import Origami.FOLD_verification.crease_pattern_verif
set_option linter.style.emptyLine false

def A : Point := ⟨0, 0⟩
def B : Point := ⟨1, 0⟩
def C : Point := ⟨1, 1⟩
def D : Point := ⟨0, 1⟩
def E : Point := ⟨0.5, 0.5⟩
def F : Point := ⟨0, 0.2⟩
def G : Point := ⟨0, 0.6⟩

def AE : Ray := ⟨A, E, Label.M⟩
def BE : Ray := ⟨B, E, Label.M⟩
def CE : Ray := ⟨C, E, Label.M⟩
def DE : Ray := ⟨D, E, Label.V⟩
def FE : Ray := ⟨F, E, Label.M⟩
def GE : Ray := ⟨G, E, Label.V⟩

def P : CreasePattern := {
  γ := {E},
  V := {A, B, C, D, F, G},
  E := {AE, BE, CE, DE, FE, GE}
}

theorem P_M : Maekawa_condition P := by
  unfold Maekawa_condition;
  intro v hv M n_M V n_V
  replace hv : v = E := hv; subst hv

  have hM : M = {AE, BE, CE, FE} := by
    ext e; unfold M P AE BE CE DE FE GE; simp; grind;


  have hV : V = {DE, GE} := by
    ext e; unfold V P AE BE CE DE FE GE; simp; grind;


  have hnM : n_M = 4 := by
    unfold n_M; rw [hM];
    unfold AE BE CE FE B F C E A; norm_num;

  have hnV : n_V = 2 := by
    unfold n_V; rw [hV];
    unfold DE GE G D E; norm_num;

  simp [hnM, hnV];
