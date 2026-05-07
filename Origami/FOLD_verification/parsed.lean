import Origami.FOLD_verification.crease_pattern_verif
set_option linter.style.emptyLine false

def A : Point := ⟨0, 0⟩
def B : Point := ⟨1, 0⟩
def C : Point := ⟨1, 1⟩
def D : Point := ⟨0, 1⟩
def E : Point := ⟨0.5, 0.5⟩
def F : Point := ⟨0, 0⟩

def AE : Ray := ⟨A, E, Label.M⟩
def BE : Ray := ⟨B, E, Label.M⟩
def CE : Ray := ⟨C, E, Label.M⟩
def DE : Ray := ⟨D, E, Label.V⟩
