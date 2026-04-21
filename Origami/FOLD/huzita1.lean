import Origami.FOLD.Properties
import Origami.FOLD.WellFormed
import Origami.FOLD.intersectionsCoextensivity

private lemma zipWith_affine_self (xs : List ℝ) (t : ℝ) :
    List.zipWith (fun a b => (1 - t) * a + t * b) xs xs = xs := by
  induction xs with
  | nil => simp
  | cons x rest ih => simp [List.zipWith, ih]; ring

theorem huzita_existence : ∀ c1 c2 : List ℝ, ∃ F : Fold, pointsOnFold F [c1, c2] := by
  intro c1 c2
  refine ⟨{ vertices := [⟨c1⟩, ⟨c2⟩],
             edges    := [⟨0, 0, EdgeType.U⟩, ⟨1, 1, EdgeType.U⟩],
             faces    := [] }, ?_⟩
  intro p hp
  simp only [List.mem_cons, List.mem_singleton] at hp
  rcases hp with rfl | rfl
  · -- c1 lies on the degenerate edge at index 0
    exact ⟨⟨0, 0, EdgeType.U⟩, List.mem_cons_self _ _, 0,
      by simp [List.get!, zipWith_affine_self]⟩
  · -- c2 lies on the degenerate edge at index 1
    exact ⟨⟨1, 1, EdgeType.U⟩, by simp, 0,
      by simp [List.get!, zipWith_affine_self]⟩
