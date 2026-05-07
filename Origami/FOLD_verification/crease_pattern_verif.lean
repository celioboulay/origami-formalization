import Mathlib

set_option linter.style.emptyLine false

structure Point where
  x : ℚ
  y : ℚ

abbrev Vertex := Point -- the vertex of the pattern

inductive Label
  | V | M
deriving DecidableEq


structure Ray where
  u : Point
  v : Point
  c : Label


structure CreasePattern where
  γ : Set Vertex
  V : Set Point
  E : Set Ray


def A : Point := ⟨0, 0⟩
def B : Point := ⟨1, 0⟩
def C : Point := ⟨1, 1⟩
def D : Point := ⟨0, 1⟩
def X : Vertex := ⟨1/2, 1/2⟩

def DX : Ray := ⟨D, X, Label.V⟩
def XB : Ray := ⟨X, B, Label.V⟩


/- assume edges are unit square -/

-- the numbers of valley and mountain folds always differ by two

def Maekawa_condition (P : CreasePattern) : Prop :=
  ∀ v ∈ P.γ,
    let M := {e ∈ P.E | e.c = Label.M}
    let n_M := M.ncard
    let V := {e ∈ P.E | e.c = Label.V}
    let n_V := V.ncard
    Int.natAbs (n_M - n_V) = 2


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




-- For Kawasaki
/- A one-vertex crease pattern consists of a set of rays or creases
drawn on a flat sheet of paper, all emanating from the same
point interior to the sheet
-/
