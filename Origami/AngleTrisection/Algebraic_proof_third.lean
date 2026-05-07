import Origami.AngleTrisection.OrigamiLib

abbrev V := EuclideanSpace ℝ (Fin 2)

/- the following "axiom" will need to be re proved as a theorem for the more complex structures -/
axiom trisection_fold_exists (B A : Point) (lθ l2 : Line) :
  ∃ f : Fold, point_on_line (fold_places_point f A) lθ ∧ point_on_line (fold_places_point f B) l2

noncomputable section

abbrev mkPoint := (EuclideanSpace.equiv (Fin 2) ℝ).symm

open Set Real
open EuclideanGeometry

def B : V := mkPoint ![0, 0]
def F : V := mkPoint ![0, 1/3]
def A : V := mkPoint ![0, 2/3]
def E : V := mkPoint ![1, 0]


def Tθ (θ : ℝ) : V :=
  mkPoint ![cos θ, sin θ]

def lθ (θ : ℝ) : Line :=
  affineSpan ℝ {B, Tθ θ}

def l2 : Line := affineSpan ℝ {F, mkPoint ![1, 1/3]}

def θ : ℝ := Real.pi / 67

def trisection_fold : Fold :=
  Classical.choose (trisection_fold_exists B A (lθ θ) l2)

def C : Point := fold_places_point trisection_fold A
def D : Point := fold_places_point trisection_fold B

/- relfection de l2 via ce fold = l3 -/
def l3 : Line := fold_places_line trisection_fold l2

/- now angle between (lθ, l2) is 1/3 of θ -/


-- (h : θ ∈ Ioo 0 Real.pi)

/- we must show θ = 3α where α = ∠DBE and θ = ∠CBE -/

-- show that ∠CBE = ∠(Tθ θ)BE since C and Tθ θ make the same line

def α : ℝ := ∠ D B E
def θ' : ℝ := ∠ C B E

lemma theta : θ = θ' := by
  unfold θ';
  sorry

lemma BDEF : ∠ D B E = ∠ B D F := by
  /- BE // DF -/
  sorry

lemma ABDF : ∠ B D F = ∠ A D F := by
  /- DF is the altitude of the isoceles triangle ABD -/
  sorry

lemma αADF : α = ∠ A D F := by
  unfold α;
  rw [BDEF, ABDF];

lemma ABCD : ∠ C B D = ∠ A D B := by
  /- ABDC is an isoceles trapezoid and ABD is an isosceles triangle,
    so ABD and BDC ar congruent isosceles triangles -/
  sorry

lemma CBD_decomp : ∠ C B D = ∠ B D F + ∠ A D F := by
  rw [ABCD];
  -- they share edge DF so they sum up to ∠ C B D
  sorry

lemma CBE_decomp : ∠ C B E = ∠ D B E + ∠ C B D :=
  -- they share the edge BG
  sorry


theorem trisection : θ = 3 * α := by
  rw [theta, θ', CBE_decomp, CBD_decomp]
  rw [← α, ← BDEF, ← α, ← αADF];
  ring;

/- blueprint of the proof -/
/- the fist 2 folds create the points A and F from B
  Then we use huzita 6 to fold (A) onto the angle's line (l_θ) while simultaneously
  placing the origin (B) onto a parallel line (l2)
  this creates points C and D
  we do't even need G in the proof
  we can now try to prove that the lines we created form a trisection of θ
  CD = AB
-/

/- Source: https://divisbyzero.com/2012/06/01/angle-trisection-using-origami/ -/
