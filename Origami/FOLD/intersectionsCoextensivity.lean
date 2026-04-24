import Origami.FOLD.Properties
import Origami.FOLD.WellFormed

def pointOnEdge (p : List ℝ) (u : List ℝ) (v : List ℝ) : Prop :=
  ∃ t : ℝ, p = List.zipWith (fun a b => (1 - t) * a + t * b) u v

def pointOnFold (F : Fold) (p : List ℝ) : Prop :=
  ∃ e ∈ F.edges,
    let pu := (F.vertices.getD e.u ⟨[]⟩).coords
    let pv := (F.vertices.getD e.v ⟨[]⟩).coords
    pointOnEdge p pu pv

def pointsOnFold (F : Fold) (ps : List (List ℝ)) : Prop :=
    ∀ p ∈ ps, pointOnFold F p

def foldsEqualUpToDirection (F1 : Fold) (F2 : Fold) : Prop :=
  ∃ e1 ∈ F1.edges, ∃ e2 ∈ F1.edges,
    let pu1 := (F1.vertices.getD e1.u ⟨[]⟩).coords
    let pv1 := (F1.vertices.getD e1.v ⟨[]⟩).coords
    let pu2 := (F2.vertices.getD e2.u ⟨[]⟩).coords
    let pv2 := (F2.vertices.getD e2.v ⟨[]⟩).coords
    pointOnEdge pu2 pu1 pv1 ∧ pointOnEdge pv2 pu1 pv1

-- Ensure this is defined before flipOverLine
def origamiDotProduct (xs ys : List ℝ) : ℝ :=
  (List.zipWith (· * ·) xs ys).sum

noncomputable def flipOverLine (p a b : List ℝ) : List ℝ :=
  let v := List.zipWith (· - ·) b a   -- Direction vector of the crease
  let w := List.zipWith (· - ·) p a   -- Vector from start of crease to point
  let v_dot_v := origamiDotProduct v v

  -- Resolve Degeneracy: If the crease length is 0, we can't reflect.
  -- Returning 'p' (or an empty list) prevents the division by zero.
  if v_dot_v = 0 then p
  else
    let scale := (origamiDotProduct w v) / v_dot_v
    let proj := v.map (fun x => x * scale)
    let foot := List.zipWith (· + ·) a proj
    -- Reflection formula: P' = 2 * Foot - P
    List.zipWith (fun f_coord p_coord => 2 * f_coord - p_coord) foot p

def pointOnPointOnceFolded (p1 : List ℝ) (p2 : List ℝ) (F : Fold) : Prop :=
  ∃ e ∈ F.edges,
    let pu := (F.vertices.getD e.u ⟨[]⟩).coords
    let pv := (F.vertices.getD e.v ⟨[]⟩).coords
    ¬ ((pointOnEdge p1 pu pv) ∨ (pointOnEdge p2 pu pv)) ∧ flipOverLine p2 pu pv = p1

def pointOnLineOnceFoldedForEdge (p1 : List ℝ) (l1 : List ℝ) (l2 : List ℝ) (e : Edge) (F : Fold) : Prop :=
  let pu := (F.vertices.getD e.u ⟨[]⟩).coords
  let pv := (F.vertices.getD e.v ⟨[]⟩).coords
  ¬ (pointOnEdge p1 pu pv) ∧ pointOnEdge (flipOverLine p1 pu pv) l1 l2

def pointOnLineOnceFolded (p1 : List ℝ) (l1 : List ℝ) (l2 : List ℝ) (F : Fold) : Prop :=
  ∃ e ∈ F.edges, pointOnLineOnceFoldedForEdge p1 l1 l2 e F

def lineOnLineOnceFolded (l11 l12 l21 l22 : List ℝ) (F : Fold) : Prop :=
  ∃ e ∈ F.edges,
    pointOnLineOnceFolded l11 l21 l22 F ∧ pointOnLineOnceFolded l12 l21 l22 F

def linesPerpendicular (a b c d : List ℝ) : Prop :=
  let v1 := List.zipWith (· - ·) b a
  let v2 := List.zipWith (· - ·) d c
  -- 1. The dot product must be zero
  origamiDotProduct v1 v2 = 0 ∧
  -- 2. Ensure neither "line" is actually just a point (Degeneracy check)
  a ≠ b ∧ c ≠ d ∧
  -- 3. Ensure they are the same dimension (Optional but recommended)
  a.length = b.length ∧ a.length = c.length ∧ c.length = d.length

def lineIsPerpendicularToFold (u v : List ℝ) (F : Fold) : Prop :=
  ∃ e ∈ F.edges,
    let pu := (F.vertices.getD e.u ⟨[]⟩).coords
    let pv := (F.vertices.getD e.v ⟨[]⟩).coords
    linesPerpendicular u v pu pv

noncomputable def magnitude (v : List ℝ) : ℝ :=
  Real.sqrt (origamiDotProduct v v)

def linesParallel (l11 l12 l21 l22 : List ℝ) : Prop :=
  let v1 := List.zipWith (· - ·) l11 l12
  let v2 := List.zipWith (· - ·) l21 l22
  abs (origamiDotProduct v1 v2) = (magnitude v1) * (magnitude v2) ∧ l11 ≠ l12 ∧ l21 ≠ l22
