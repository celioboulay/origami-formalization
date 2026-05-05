import Origami.Huzita.Structures

/- Axiom 1:
  Given two points p1 and p2, there is a unique fold that passes through both of them.
-/

axiom huzita_1 (p1 p2 : Point) :
  ∃! f : Fold, f_through_p f p1 ∧ f_through_p f p2


/- Axiom 2:
  Given two points p1 and p2, there is a unique fold that places p1 onto p2.
-/

axiom huzita_2 (p1 p2 : Point) :
  ∃! f : Fold, f_places_p f p1 = p2


/- Axiom 3:
  Given two lines l1 and l2, there is a fold that places l1 onto l2 -/

axiom huzita_3 (l1 l2 : Line) :
  ∃! f : Fold, f_places_l f l1 = l2


/- Axiom 4: Given a point p1 and a line l1, there is a
  unique fold perpendicular to l1 that passes through point p1 -/

axiom huzita_4 (p1 : Point) (l1 : Line) :
  ∃! f : Fold, perpendicular f l1 ∧ f_through_p f p1


/- Axiom 5: Given two points p1 and p2 and a line l1,
  there is a fold that places p1 onto l1 and passes through p2 -/

axiom huzita_5 (p1 p2 : Point) (l1 : Line) :
  ∃ f : Fold, f_through_p f p2 ∧ on_line l1 (f_places_p f p1)


/- Axiom 6: Given two points p1 and p2 and two lines l1 and l2
  there is a fold that places p1 onto l1 and p2 onto l2 -/

axiom huzita_6 (p1 p2 : Point) (l1 l2 : Line) :
  ∃ f : Fold, on_line l1 (f_places_p f p1) ∧ on_line l2 (f_places_p f p2)


/- Axiom 7: Given one point p and two lines l1 and l2 that aren't parallel,
there is a fold that places p onto l1 and is perpendicular to l2 -/

axiom huzita_7 (p : Point) (l1 l2 : Line) (h : ¬ parallel l1 l2) :
  ∃ f : Fold, on_line l1 (f_places_p f p) ∧ perpendicular f l2
