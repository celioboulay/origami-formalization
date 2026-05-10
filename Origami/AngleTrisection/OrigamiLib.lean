import Mathlib

set_option linter.style.whitespace false

abbrev Point := EuclideanSpace ℝ (Fin 2)
abbrev Line := AffineSubspace ℝ Point
abbrev Fold := Line

noncomputable section

def point_on_segment (p a b : Point) : Prop :=
  ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ p = (1 - t) • a + t • b


def fold_places_point (f : Fold) (p : Point) : Point := by
  by_cases hne : Nonempty f
  case pos =>
    letI : Nonempty f := hne
    exact EuclideanGeometry.reflection f p
  case neg =>
    exact p

def fold_places_line (f : Fold) (l : Line) : Line := by
  by_cases hne : Nonempty f
  case pos =>
    letI : Nonempty f := hne
    exact l.map (EuclideanGeometry.reflection f).toAffineMap
  case neg => exact l


def point_on_line (p : Point) (L : Line) : Prop := p ∈ L


def lines_perpendicular (l1 l2 : Line) : Prop :=
  l1.direction ⟂ l2.direction


def lines_parallel (l1 l2 : Line) : Prop :=
  l1.direction = l2.direction

end
