import OriginalCounitRightConeQJoinedCofaceReconciled

/-!
# Vertex formula for the actual augmented-simplex join map

The original `joinHom` acts as `α` on the old vertices and fixes the
appended terminal vertex. These two equations make its image usable
in the common-face calculation without replacing the literal cone.
-/

set_option autoImplicit false

open CategoryTheory Simplicial
open DaggerOriginalCounitRightConeFunctor

namespace DaggerOriginalCounitRightConeQJoinVertexFormula

noncomputable section

/-- On old vertices, `joinHom α` is `α` with a final vertex appended. -/
theorem joinHom_castSucc {m n : SimplexCategory} (α : m ⟶ n)
    (v : Fin (m.len + 1)) :
    (joinHom α).toOrderHom v.castSucc =
      (α.toOrderHom v).castSucc := by
  have hleft := AugmentedSimplexCategory.inl_comp_tensorHom
    (AugmentedSimplexCategory.inclusion.map α)
    (𝟙 (AugmentedSimplexCategory.inclusion.obj (SimplexCategory.mk 0)))
  change AugmentedSimplexCategory.inl' m ⦋0⦌ ≫ joinHom α =
    α ≫ AugmentedSimplexCategory.inl' n ⦋0⦌ at hleft
  have hv := congrFun (congrArg (fun f ↦ f.toOrderHom) hleft) v
  change (joinHom α).toOrderHom
      ((AugmentedSimplexCategory.inl' m ⦋0⦌).toOrderHom v) =
    (AugmentedSimplexCategory.inl' n ⦋0⦌).toOrderHom
      (α.toOrderHom v) at hv
  have hm : (AugmentedSimplexCategory.inl' m ⦋0⦌).toOrderHom v =
      v.castSucc := by
    rw [AugmentedSimplexCategory.inl'_eval]
    apply Fin.ext
    rfl
  have hn : (AugmentedSimplexCategory.inl' n ⦋0⦌).toOrderHom
      (α.toOrderHom v) = (α.toOrderHom v).castSucc := by
    rw [AugmentedSimplexCategory.inl'_eval]
    apply Fin.ext
    rfl
  simpa only [hm, hn] using hv

/-- The appended terminal vertex is fixed by `joinHom α`. -/
theorem joinHom_last {m n : SimplexCategory} (α : m ⟶ n) :
    (joinHom α).toOrderHom (Fin.last (m.len + 1)) =
      Fin.last (n.len + 1) := by
  have hright := AugmentedSimplexCategory.inr_comp_tensorHom
    (AugmentedSimplexCategory.inclusion.map α)
    (𝟙 (AugmentedSimplexCategory.inclusion.obj (SimplexCategory.mk 0)))
  change AugmentedSimplexCategory.inr' m ⦋0⦌ ≫ joinHom α =
    𝟙 (SimplexCategory.mk 0) ≫
      AugmentedSimplexCategory.inr' n ⦋0⦌ at hright
  have hv := congrFun (congrArg (fun f ↦ f.toOrderHom) hright) (0 : Fin 1)
  change (joinHom α).toOrderHom
      ((AugmentedSimplexCategory.inr' m ⦋0⦌).toOrderHom 0) =
    (AugmentedSimplexCategory.inr' n ⦋0⦌).toOrderHom 0 at hv
  have hm : (AugmentedSimplexCategory.inr' m ⦋0⦌).toOrderHom 0 =
      Fin.last (m.len + 1) := by
    rw [AugmentedSimplexCategory.inr'_eval]
    apply Fin.ext
    simp
  have hn : (AugmentedSimplexCategory.inr' n ⦋0⦌).toOrderHom 0 =
      Fin.last (n.len + 1) := by
    rw [AugmentedSimplexCategory.inr'_eval]
    apply Fin.ext
    simp
  simpa only [hm, hn] using hv

end

end DaggerOriginalCounitRightConeQJoinVertexFormula
