import Mathlib

/- Structures -/
structure Point where -- using ℚ instead of ℝ to make things computable
  x : ℚ
  y : ℚ

structure Line where -- line
  a : ℚ
  b : ℚ
  c : ℚ
  nontrivial : a ≠ 0 ∨ b ≠ 0
  normalized : a = 1 ∨ a = 0 ∧ b = 1

abbrev Fold := Line
-- a Fold is the same thing as a line but we use this abbrev to distinguish between both types


def f_through_p (f : Fold) (p : Point) : Prop :=
  f.a * p.x + f.b + p.y + f.c = 0

def on_line (l : Line) (p : Point) : Prop :=
  l.a * p.x + l.b + p.y + l.c = 0 -- same as above but different names

def f_places_p (f : Fold) (p : Point) : Point :=
  let d := (f.a * p.x + f.b * p.y + f.c) / (f.a^2 + f.b^2)
  { x := p.x - 2 * f.a * d
    y := p.y - 2 * f.b * d }


def f_places_l (f : Fold) (l : Line) : Line := -- Gemini for norm and nontrivial
  let norm := f.a * f.a + f.b * f.b
  let a' := l.a * (f.b * f.b - f.a * f.a) - 2 * l.b * f.a * f.b
  let b' := l.b * (f.a * f.a - f.b * f.b) - 2 * l.a * f.a * f.b
  let c' := l.c * norm + 2 * f.c * (l.a * f.a + l.b * f.b)
  have h_nt : a' ≠ 0 ∨ b' ≠ 0 := by
    by_contra h; push Not at h; obtain ⟨h_a, h_b⟩ := h
    have h_id : a'^2 + b'^2 = (l.a^2 + l.b^2) * (f.a^2 + f.b^2)^2 := by dsimp [a', b']; ring;
    rw [h_a, h_b] at h_id; norm_num at h_id
    have h_c_pos : 0 < f.a^2 + f.b^2 := by rcases f.nontrivial with ha | hb <;> positivity
    have h_l_pos : 0 < l.a^2 + l.b^2 := by rcases l.nontrivial with hla | hlb <;> positivity
    have : 0 < (l.a^2 + l.b^2) * (f.a^2 + f.b^2)^2 := by positivity
    nlinarith
  { a := if a' ≠ 0 then 1 else 0
    b := if ha : a' ≠ 0 then b' / a' else 1
    c := if ha : a' ≠ 0 then c' / a' else c' / b'
    nontrivial := by
      split_ifs <;> simp [one_ne_zero]
    normalized := by
      split_ifs with ha
      · left; rfl
      · right; exact ⟨rfl, rfl⟩
  }

/- States that two lines are ⟂, can be used for both folds and lines -/
def perpendicular (l1 l2 : Line) : Prop := l1.a * l2.a + l1.b * l2.b = 0

def parallel (l1 l2 : Line) : Prop := l1.a * l2.b - l2.a * l1.b = 0
