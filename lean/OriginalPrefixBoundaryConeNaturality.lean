import OriginalRestPrefixBoundaryFunctor

/-!
# Exact suffix-operator naturality of the original cone unit

The native successor join maps commute with prepending on the exact original
ambient simplices. This yields naturality of the original cone unit in every
suffix degree, retaining the actual smaller and remaining boundary operators.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerOriginalOrdinalJoinLeft DaggerOriginalSimplexCoslice
open DaggerOriginalJoinedHornGeometry DaggerOriginalJoinedCofaces
open DaggerOriginalJoinedPrefixBoundaryFunctor
open DaggerOriginalPrefixDeleteFirstNativeJoin
open DaggerOriginalPrefixBoundaryConeOperators DaggerOriginalPrefixBoundaryConeUnit
open DaggerOriginalRestPrefixBoundaryFunctor

universe u

namespace DaggerOriginalPrefixBoundaryConeNaturality

/-- Every original suffix operator commutes with the actual native cone operator. -/
theorem prefixConeOperator_target_comp (k : ℕ) {m n d : SimplexCategory}
    (β : m ⟶ n) (α : d ⟶ ⦋k + m.len + 1⦌) :
    prefixConeOperator k n.len (α ≫ (ordinalJoinLeft ⦋k⦌).map β) =
      prefixConeOperator k m.len α ≫ (ordinalJoinLeft ⦋k + 1⦌).map β := by
  induction m using SimplexCategory.rec with | h m =>
    induction n using SimplexCategory.rec with | h n =>
      induction d using SimplexCategory.rec with | h d =>
        have hright : AugmentedSimplexCategory.inr' ⦋0⦌ ⦋d⦌ ≫
            prefixConeOperator k n (α ≫ (ordinalJoinLeft ⦋k⦌).map β) =
          AugmentedSimplexCategory.inr' ⦋0⦌ ⦋d⦌ ≫
            (prefixConeOperator k m α ≫ (ordinalJoinLeft ⦋k + 1⦌).map β) := by
          rw [prefixConeOperator_suffix_comp, ← Category.assoc,
            prefixConeOperator_suffix_comp]
          rw [Category.assoc, prefixDeleteFirstOperator_naturality, Category.assoc]
        apply SimplexCategory.Hom.ext
        apply OrderHom.ext
        funext a
        rcases vertex_eq_prefix_or_suffix 0 d a with ⟨b, rfl⟩ | ⟨b, rfl⟩
        · apply Fin.ext
          rw [prefixIndex_eq_native]
          change ((prefixConeOperator k n (α ≫ (ordinalJoinLeft ⦋k⦌).map β)).toOrderHom
              ((AugmentedSimplexCategory.inl' ⦋0⦌ ⦋d⦌).toOrderHom b)).val =
            (((ordinalJoinLeft ⦋k + 1⦌).map β).toOrderHom
              ((prefixConeOperator k m α).toOrderHom
                ((AugmentedSimplexCategory.inl' ⦋0⦌ ⦋d⦌).toOrderHom b))).val
          have hz : (prefixConeOperator k m α).toOrderHom
              ((AugmentedSimplexCategory.inl' ⦋0⦌ ⦋d⦌).toOrderHom b) =
                prefixIndex (k + 1) m 0 :=
            Fin.ext (prefixConeOperator_prefix_eval k m α b)
          rw [prefixConeOperator_prefix_eval, hz, joinMap_prefix_eval]
          rfl
        · rw [suffixIndex_eq_native]
          exact congrArg (fun f ↦ f.toOrderHom b) hright

/-- The cone unit commutes with the exact smaller and remaining boundary operators. -/
theorem prefixConeBoundaryUnit_naturality (k : ℕ) {m n : SimplexCategory} (β : m ⟶ n) :
    prefixBoundaryMap.{u} k β ≫ prefixConeBoundaryUnit k n.len =
      prefixConeBoundaryUnit k m.len ≫
        Functor.whiskerLeft (ordinalJoinLeft ⦋0⦌).op (restPrefixBoundaryMap k β) := by
  ext q s
  apply Subtype.ext
  apply SSet.stdSimplex.objEquiv.injective
  change prefixConeOperator k n.len
      (SSet.stdSimplex.objEquiv s.val ≫ (ordinalJoinLeft ⦋k⦌).map β) =
    prefixConeOperator k m.len (SSet.stdSimplex.objEquiv s.val) ≫
      (ordinalJoinLeft ⦋k + 1⦌).map β
  exact prefixConeOperator_target_comp k β _

end DaggerOriginalPrefixBoundaryConeNaturality
