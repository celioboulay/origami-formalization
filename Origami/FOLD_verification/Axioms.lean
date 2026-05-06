import Origami.FOLD_verification.EuclideanMathlib

set_option linter.style.longLine false


/- Axiom 1:
  Given two points p1 and p2, there is a unique fold that passes through both of them.
-/

axiom huzita_1 (p1 p2 : Point) (h : p1 ≠ p2) :
  ∃! crease : AffineSubspace ℝ Point, lineLike crease ∧ pointOnLine p1 crease ∧ pointOnLine p2 crease


/- Axiom 2:
  Given two points p1 and p2, there is a unique fold that places p1 onto p2.
-/

axiom huzita_2 (p1 p2 : Point) (h : p1 ≠ p2) :
  ∃! crease : AffineSubspace ℝ Point, lineLike crease ∧ foldOverCrease crease p1 = p2


/- Axiom 3:
  Given two lines l1 and l2, there is a fold that places l1 onto l2 -/

axiom huzita_3 (l1 l2 : AffineSubspace ℝ Point) (hl1 : lineLike l1) (hl2 : lineLike l2) :
  ∃ crease : AffineSubspace ℝ Point, lineLike crease ∧ foldsLineOntoLine crease l1 l2


/- Axiom 4: Given a point p1 and a line l1, there is a
  unique fold perpendicular to l1 that passes through point p1 -/

axiom huzita_4 (p1 : Point) (l1 : AffineSubspace ℝ Point) (hl1 : lineLike l1) :
  ∃! crease : AffineSubspace ℝ Point, lineLike crease ∧ linesPerpendicular crease l1 ∧ pointOnLine p1 crease


/- Axiom 5: Given two points p1 and p2 and a line l1,
  there is a fold that places p1 onto l1 and passes through p2 -/

axiom huzita_5 (p1 p2 : Point) (l1 : AffineSubspace ℝ Point) (hl1 : lineLike l1) :
  ∃ crease : AffineSubspace ℝ Point, lineLike crease ∧ pointOnLine p2 crease ∧ foldsPointOntoLine crease l1 p1


/- Axiom 6: Given two points p1 and p2 and two lines l1 and l2
  there is a fold that places p1 onto l1 and p2 onto l2 -/

axiom huzita_6 (p1 p2 : Point) (l1 l2 : AffineSubspace ℝ Point) (hl1 : lineLike l1) (hl2 : lineLike l2) :
  ∃ crease : AffineSubspace ℝ Point, lineLike crease ∧ foldsPointOntoLine crease l1 p1 ∧ foldsPointOntoLine crease l2 p2


/- Axiom 7: Given one point p and two lines l1 and l2 that aren't parallel,
there is a fold that places p onto l1 and is perpendicular to l2 -/

axiom huzita_7 (p : Point) (l1 l2 : AffineSubspace ℝ Point) (hl1 : lineLike l1) (hl2 : lineLike l2) (h : ¬ linesParallel l1 l2) :
  ∃ crease : AffineSubspace ℝ Point, lineLike crease ∧ foldsPointOntoLine crease l1 p ∧ linesPerpendicular crease l2
