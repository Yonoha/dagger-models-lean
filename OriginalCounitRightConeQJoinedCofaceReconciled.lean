import OriginalCounitRightConeFunctor

/-!
# Joined cosimplicial cofaces are literal standard-simplex cofaces

Appending the terminal ordinal point sends an old coface `δ_i` to the
coface omitting the same old vertex. The proof checks the two summands of
the original augmented-simplex tensor using its `inl`/`inr` naturality;
it does not replace the collapsed-face right cone by a simplex.
-/

set_option autoImplicit false

open CategoryTheory Simplicial
open DaggerOriginalCounitRightConeFunctor

universe u

namespace DaggerOriginalCounitRightConeQJoinedCoface

noncomputable section

private theorem inl_vertex (n : ℕ) (v : Fin (n + 1)) :
    (AugmentedSimplexCategory.inl' ⦋n⦌ ⦋0⦌).toOrderHom v =
      v.castSucc := by
  rw [AugmentedSimplexCategory.inl'_eval]
  apply Fin.ext
  rfl

private theorem inr_vertex (n : ℕ) :
    (AugmentedSimplexCategory.inr' ⦋n⦌ ⦋0⦌).toOrderHom (0 : Fin 1) =
      Fin.last (n + 1) := by
  rw [AugmentedSimplexCategory.inr'_eval]
  apply Fin.ext
  simp

/-- `joinHom` of the original coface is the standard coface omitting the
same old vertex, with the appended terminal vertex preserved. -/
theorem joinHom_delta (k : ℕ) (i : Fin (k + 2)) :
    joinHom (SimplexCategory.δ i) =
      SimplexCategory.δ i.castSucc := by
  have hleft := AugmentedSimplexCategory.inl_comp_tensorHom
    (AugmentedSimplexCategory.inclusion.map (SimplexCategory.δ i))
    (𝟙 (AugmentedSimplexCategory.inclusion.obj (SimplexCategory.mk 0)))
  change AugmentedSimplexCategory.inl' ⦋k⦌ ⦋0⦌ ≫
      joinHom (SimplexCategory.δ i) =
        SimplexCategory.δ i ≫
          AugmentedSimplexCategory.inl' ⦋k + 1⦌ ⦋0⦌ at hleft
  have hright := AugmentedSimplexCategory.inr_comp_tensorHom
    (AugmentedSimplexCategory.inclusion.map (SimplexCategory.δ i))
    (𝟙 (AugmentedSimplexCategory.inclusion.obj (SimplexCategory.mk 0)))
  change AugmentedSimplexCategory.inr' ⦋k⦌ ⦋0⦌ ≫
      joinHom (SimplexCategory.δ i) =
        𝟙 (SimplexCategory.mk 0) ≫
          AugmentedSimplexCategory.inr' ⦋k + 1⦌ ⦋0⦌ at hright
  ext v : 3
  cases v using Fin.lastCases with
  | last =>
      have hv := congrFun (congrArg (fun f ↦ f.toOrderHom) hright) (0 : Fin 1)
      change (joinHom (SimplexCategory.δ i)).toOrderHom
          ((AugmentedSimplexCategory.inr' ⦋k⦌ ⦋0⦌).toOrderHom 0) =
        (AugmentedSimplexCategory.inr' ⦋k + 1⦌ ⦋0⦌).toOrderHom 0 at hv
      rw [inr_vertex k, inr_vertex (k + 1)] at hv
      change (joinHom (SimplexCategory.δ i)).toOrderHom (Fin.last (k + 1)) =
        i.castSucc.succAbove (Fin.last (k + 1))
      rw [Fin.succAbove_of_le_castSucc i.castSucc (Fin.last (k + 1))
        (Fin.castSucc_le_castSucc_iff.mpr (Fin.le_last i))]
      simpa using hv
  | cast v =>
      have hv := congrFun (congrArg (fun f ↦ f.toOrderHom) hleft) v
      change (joinHom (SimplexCategory.δ i)).toOrderHom
          ((AugmentedSimplexCategory.inl' ⦋k⦌ ⦋0⦌).toOrderHom v) =
        (AugmentedSimplexCategory.inl' ⦋k + 1⦌ ⦋0⦌).toOrderHom
          ((SimplexCategory.δ i).toOrderHom v) at hv
      rw [inl_vertex k v,
        inl_vertex (k + 1) ((SimplexCategory.δ i).toOrderHom v)] at hv
      change (joinHom (SimplexCategory.δ i)).toOrderHom v.castSucc =
        i.castSucc.succAbove v.castSucc
      rw [Fin.castSucc_succAbove_castSucc]
      exact hv

/-- The large-simplex map of a literal cone coface is the corresponding
standard-simplex face map. -/
theorem joinMap_delta (k : ℕ) (i : Fin (k + 2)) :
    joinMap.{u} (SimplexCategory.δ i) =
      SSet.stdSimplex.δ i.castSucc := by
  simp only [joinMap, joinHom_delta]
  rfl

end

end DaggerOriginalCounitRightConeQJoinedCoface
