import NativeRightConeSimplexPresentation

/-! Cofaces of the original appended-vertex join retain the original coface indices. -/
set_option autoImplicit false
open CategoryTheory Simplicial
open DaggerOriginalCounitRightConeFunctor
universe u
namespace DaggerNativeRightConeCofaceGeometry

theorem joinHom_prefix {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌) (j : Fin (m + 1)) :
    (joinHom α).toOrderHom j.castSucc = (α.toOrderHom j).castSucc := by
  have h := AugmentedSimplexCategory.inl_comp_tensorHom
    (AugmentedSimplexCategory.inclusion.map α)
    (𝟙 (AugmentedSimplexCategory.inclusion.obj ⦋0⦌))
  change AugmentedSimplexCategory.inl' ⦋m⦌ ⦋0⦌ ≫ joinHom α =
    α ≫ AugmentedSimplexCategory.inl' ⦋n⦌ ⦋0⦌ at h
  have he := congrArg (fun f ↦ f.toOrderHom j) h
  change (joinHom α).toOrderHom
    ((AugmentedSimplexCategory.inl' ⦋m⦌ ⦋0⦌).toOrderHom j) =
    (AugmentedSimplexCategory.inl' ⦋n⦌ ⦋0⦌).toOrderHom (α.toOrderHom j) at he
  rw [AugmentedSimplexCategory.inl'_eval, AugmentedSimplexCategory.inl'_eval] at he
  exact he

theorem joinHom_last {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌) :
    (joinHom α).toOrderHom (Fin.last (m + 1)) = Fin.last (n + 1) := by
  have h := AugmentedSimplexCategory.inr_comp_tensorHom
    (AugmentedSimplexCategory.inclusion.map α)
    (𝟙 (AugmentedSimplexCategory.inclusion.obj ⦋0⦌))
  change AugmentedSimplexCategory.inr' ⦋m⦌ ⦋0⦌ ≫ joinHom α =
    𝟙 ⦋0⦌ ≫ AugmentedSimplexCategory.inr' ⦋n⦌ ⦋0⦌ at h
  have he := congrArg (fun f ↦ f.toOrderHom 0) h
  change (joinHom α).toOrderHom
    ((AugmentedSimplexCategory.inr' ⦋m⦌ ⦋0⦌).toOrderHom 0) =
    (AugmentedSimplexCategory.inr' ⦋n⦌ ⦋0⦌).toOrderHom 0 at he
  rw [AugmentedSimplexCategory.inr'_eval, AugmentedSimplexCategory.inr'_eval] at he
  exact he

theorem joinHom_coface {n : ℕ} (i : Fin (n + 2)) :
    joinHom (SimplexCategory.δ i) = SimplexCategory.δ i.castSucc := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext j
  by_cases hj : j.val < n + 1
  · obtain ⟨a, rfl⟩ : ∃ a : Fin (n + 1), a.castSucc = j := by
      exact ⟨⟨j.val, hj⟩, Fin.ext rfl⟩
    rw [joinHom_prefix]
    change (i.succAbove a).castSucc = i.castSucc.succAbove a.castSucc
    by_cases ha : a.castSucc < i
    · rw [Fin.succAbove_of_castSucc_lt i a ha,
        Fin.succAbove_of_castSucc_lt i.castSucc a.castSucc (by
          change a.val < i.val
          exact ha)]
    · have h := le_of_not_gt ha
      rw [Fin.succAbove_of_le_castSucc i a h,
        Fin.succAbove_of_le_castSucc i.castSucc a.castSucc (by
          change i.val ≤ a.val
          exact h)]
      exact Fin.ext rfl
  · have hlast : j = Fin.last (n + 1) := by
      apply Fin.ext
      change j.val = n + 1
      have ht : j.val < n + 2 := j.isLt
      omega
    rw [hlast, joinHom_last]
    change Fin.last (n + 2) = i.castSucc.succAbove (Fin.last (n + 1))
    rw [Fin.succAbove_of_le_castSucc _ _ (by
      change i.val ≤ n + 1
      have ht := i.isLt
      omega)]
    rfl

theorem joinMap_coface {n : ℕ} (i : Fin (n + 2)) :
    joinMap.{u} (SimplexCategory.δ i) = SSet.stdSimplex.δ i.castSucc := by
  exact congrArg SSet.stdSimplex.map (joinHom_coface i)

end DaggerNativeRightConeCofaceGeometry
