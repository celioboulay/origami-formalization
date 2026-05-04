import Mathlib

/- Structures -/
structure Vertex where -- using ℚ instead of ℝ to make things computable
  x : ℚ
  y : ℚ
deriving instance BEq, ReflBEq, LawfulBEq, DecidableEq for Vertex

structure Face where -- triangle | vertices counter-clockwise
  id : ℕ
  v0 : Vertex
  v1 : Vertex
  v2 : Vertex
deriving instance BEq, DecidableEq for Face

abbrev FacePair := Face × Face

structure Fold where
  faces : Set Face
  f_o : Set FacePair -- or define new order relation

structure Crease where -- line
  a : ℚ
  b : ℚ
  c : ℚ
  nontrivial : a ≠ 0 ∨ b ≠ 0
