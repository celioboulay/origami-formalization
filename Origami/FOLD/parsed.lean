import Origami.FOLD.Data.Properties
import Origami.FOLD.Data.WellFormed
import Origami.FOLD.Bridge.DataToMath
set_option linter.style.emptyLine false

noncomputable section
open Origami.FOLD.Bridge

def v0 : Vertex := {coords := [0, 1, 0]}
def v1 : Vertex := {coords := [0, 0, 1]}
def v2 : Vertex := {coords := [0, -1, 0]}
def v3 : Vertex := {coords := [1, 0, 0]}
def v4 : Vertex := {coords := [0, 0, -1]}
def v5 : Vertex := {coords := [0, 0, -1]}

def f0 : Face := {verts := [0, 1, 2]}
def f1 : Face := {verts := [0, 2, 3]}
def f2 : Face := {verts := [0, 4, 1]}
def f3 : Face := {verts := [1, 5, 2]}

def e0 : Edge := {u := 0, v := 2, assignment := EdgeType.V}
def e1 : Edge := {u := 0, v := 1, assignment := EdgeType.M}
def e2 : Edge := {u := 1, v := 2, assignment := EdgeType.M}
def e3 : Edge := {u := 2, v := 3, assignment := EdgeType.B}
def e4 : Edge := {u := 0, v := 3, assignment := EdgeType.B}
def e5 : Edge := {u := 1, v := 4, assignment := EdgeType.B}
def e6 : Edge := {u := 1, v := 5, assignment := EdgeType.B}
def e7 : Edge := {u := 0, v := 4, assignment := EdgeType.B}
def e8 : Edge := {u := 2, v := 5, assignment := EdgeType.B}

def F : Fold := {
  vertices := [v0, v1, v2, v3, v4, v5],
  edges    := [e0, e1, e2, e3, e4, e5, e6, e7, e8],
  faces    := [f0, f1, f2, f3]
}

def parsedBridgeReady : Prop :=
  BridgeReady F

def parsedWellFormed2D : Prop :=
  WellFormed2D F

def parsedCreases : List (AffineSubspace Real Point2D) :=
  foldToCreases F

theorem parsedBridgeReady_iff_wellFormed2D :
    parsedBridgeReady ↔ parsedWellFormed2D := by
  simpa [parsedBridgeReady, parsedWellFormed2D] using
    (bridgeReady_iff_wellFormed2D F)

theorem parsedEdgeCrease_exists
    (hReady : parsedBridgeReady) {e : Edge} (he : e ∈ F.edges) :
    ∃ crease : AffineSubspace Real Point2D, edgeToCrease F e = some crease := by
  simpa [parsedBridgeReady] using edgeToCrease_exists_of_bridgeReady (F := F) hReady he

end
