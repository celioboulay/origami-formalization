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


-- (h : θ ∈ Ioo 0 Real.pi)


lemma ez {θ : ℝ} : θ = θ/3 + θ/3 + θ/3 := by
  linarith

/- blueprint of the proof -/
/- the fist 2 folds create the points A and F from B
  Then we use huzita 6 to fold (A) onto the angle's line (l_θ) while simultaneously
  placing the origin (B) onto a parallel line (l2)
  this creates points C and D
  we then add point G at the intersection of lθ and the fold from axiom6
  we can now try to prove that the lines we created form a trisection of θ
  CD = AB
-/
