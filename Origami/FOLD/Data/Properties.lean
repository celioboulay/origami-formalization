import Mathlib

/-- Basic geometry container (dimension-agnostic) -/
structure Vertex where
  coords : List ℝ

inductive EdgeType
| V | M | F | U | B
deriving DecidableEq

/-- Faces and edges use indices into global arrays -/
structure Edge where
  u : Nat
  v : Nat
  assignment : EdgeType

structure Face where
  verts : List Nat

structure Fold where
  vertices : List Vertex
  edges    : List Edge
  faces    : List Face
