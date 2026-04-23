import Origami.FOLD.Properties
import Origami.FOLD.WellFormed
import Origami.FOLD.intersectionsCoextensivity

private lemma zipWith_affine_self (xs : List ℝ) (t : ℝ) :
    List.zipWith (fun a b => (1 - t) * a + t * b) xs xs = xs := by
  induction xs with
  | nil => simp [List.zipWith]
  | cons x rest ih =>
    simp [List.zipWith]
    constructor
    · ring -- Solves: (1 - t) * x + t * x = x
    · -- This part proves: List.map (fun a => (1 - t) * a + t * a) rest = rest
      simp_rw [show ∀ a, (1 - t) * a + t * a = a by intro a; ring]
      simp

theorem huzita_existence : ∀ c1 c2 : List ℝ, c1.length = c2.length → ∃ F : Fold, pointsOnFold F [c1, c2] := by
  intro c1 c2 hlen
  -- We define a Fold with one edge connecting vertex 0 (c1) and vertex 1 (c2)
  refine ⟨{
    vertices := [⟨c1⟩, ⟨c2⟩],
    edges    := [⟨0, 1, EdgeType.U⟩],
    faces    := []
  }, ?_⟩
  simp [pointsOnFold]
  constructor
  · -- Case: p = c1
    -- We pick edge 0 and set t = 0 (the start of the edge)
    refine ⟨⟨0, 1, EdgeType.U⟩, by simp, 0, ?_⟩
    -- This simplifies to: c1 = zipWith (λ a b => a) c1 c2
    simp
    -- Proving: c1 = zipWith (λ a _ => a) c1 c2
    induction c1 generalizing c2 with
    | nil => simp
    | cons x rest ih =>
      cases c2 with
      | nil => simp at hlen
      | cons y rs =>
        simp [List.zipWith]
        apply ih
        simp at hlen; exact hlen
  · -- Case: p = c2
    -- We pick edge 0 and set t = 1 (the end of the edge)
    refine ⟨⟨0, 1, EdgeType.U⟩, by simp, 1, ?_⟩
    -- This simplifies to: c2 = zipWith (λ a b => b) c1 c2
    simp
    induction c1 generalizing c2 with
    | nil =>
      cases c2 with | nil => simp | cons y rs => simp at hlen
    | cons x rest ih =>
      cases c2 with
      | nil => simp at hlen
      | cons y rs =>
        simp [List.zipWith]
        apply ih
        simp at hlen; exact hlen
