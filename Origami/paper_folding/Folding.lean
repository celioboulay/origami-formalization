import Origami.paper_folding.GoodProperties

/- Basic geometry -/
def A : Vertex := {x := 0, y := 0}
def B : Vertex := {x := 1, y := 0}
def C : Vertex := {x := 1, y := 1}
def D : Vertex := {x := 0, y := 1}

def f0 : Face := {id := 0, v0 := A, v1 := B, v2 := C}
def f1 : Face := {id := 1, v0 := A, v1 := C, v2 := D}

def F0 : Fold := {
  faces := {f0, f1},
  f_o := ∅
}

/- transition relation -/
def step_rel (F G : Fold) : Prop :=
  ∃ S : Step, S.F = F ∧ S.G = G ∧ valid_step S

/- Reachability -/
inductive Reach : Fold → Fold → Prop
  | refl (F) : Reach F F
  | step (F G H) :
      step_rel F G →
      Reach G H →
      Reach F H

/- Main definition -/
def origami_possible (F : Fold) : Prop :=
  Reach F0 F
