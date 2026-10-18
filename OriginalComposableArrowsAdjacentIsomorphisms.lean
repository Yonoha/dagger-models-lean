import OriginalInnerHornFillers

/-!
# Adjacent isomorphisms in an actual composable-arrow diagram

All arrows in a finite ordered diagram are composites of adjacent arrows.
This is used for the original nerve-unit core predicate on inner-horn fillers.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial

universe v u

namespace DaggerOriginalComposableArrowsAdjacentIsomorphisms

/-- The actual arrow between adjacent finite ordered vertices. -/
def adjacentHom {n : ℕ} (k : Fin n) :
    (k.castSucc : Fin (n + 1)) ⟶ k.succ := homOfLE (Fin.castSucc_le_succ k)

/-- Adjacent invertibility implies invertibility of every original arrow in the diagram. -/
theorem all_arrows_iso_of_adjacent {C : Type u} [Category.{v} C] {n : ℕ}
    (s : ComposableArrows C n) (h : ∀ k : Fin n, IsIso (s.map (adjacentHom k))) :
    ∀ {i j : Fin (n + 1)} (f : i ⟶ j), IsIso (s.map f) := by
  intro i j
  induction j using Fin.induction with
  | zero =>
    intro f
    have hi : i = 0 := by
      apply Fin.ext
      simp only [Fin.val_zero]
      have hf := leOfHom f
      change i.val ≤ 0 at hf
      omega
    subst i
    have hf : f = 𝟙 (0 : Fin (n + 1)) := Subsingleton.elim _ _
    rw [hf, s.map_id]
    infer_instance
  | succ j ih =>
    intro f
    by_cases hi : i = j.succ
    · subst i
      have hf : f = 𝟙 j.succ := Subsingleton.elim _ _
      rw [hf, s.map_id]
      infer_instance
    · have hij : i ≤ j.castSucc := by
        have hf := leOfHom f
        have hne : i.val ≠ j.val + 1 := by
          intro hv
          exact hi (Fin.ext hv)
        change i.val ≤ j.val + 1 at hf
        change i.val ≤ j.val
        omega
      let g : i ⟶ j.castSucc := homOfLE hij
      have : IsIso (s.map g) := ih g
      have : IsIso (s.map (adjacentHom j)) := h j
      have hf : f = g ≫ adjacentHom j := Subsingleton.elim _ _
      rw [hf, s.map_comp]
      infer_instance

end DaggerOriginalComposableArrowsAdjacentIsomorphisms
