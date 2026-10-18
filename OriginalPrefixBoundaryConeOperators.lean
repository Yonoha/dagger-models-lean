import OriginalZeroJoinYonedaCorrespondence
import OriginalJoinedCofaces

/-!
# Original cone operators into the remaining successor boundary

Prepend the native vertex join and retain the explicit original ambient cast.
The operator commutes with all domain operators and restricts on the right
block to the original first-prefix coface. No filling assumption is used.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerOriginalOrdinalJoinLeft DaggerOriginalJoinedHornGeometry
open DaggerOriginalJoinedCofaces DaggerOriginalPrefixDeleteFirstCoface

universe u

namespace DaggerOriginalPrefixBoundaryConeOperators

/-- The exact native cone ambient object is the original successor ambient object. -/
def coneAmbientIso (k n : ℕ) :
    (ordinalJoinLeft ⦋0⦌).obj ⦋k + n + 1⦌ ≅ ⦋k + 1 + n + 1⦌ :=
  eqToIso (congrArg SimplexCategory.mk (show 0 + (k + n + 1) + 1 = k + 1 + n + 1 by
    omega))

/-- The ambient cast preserves every original vertex value. -/
theorem coneAmbientIso_hom_eval (k n : ℕ) (i : Fin (0 + (k + n + 1) + 2)) :
    ((coneAmbientIso k n).hom.toOrderHom i).val = i.val := by
  rw [coneAmbientIso, eqToIso.hom, SimplexCategory.eqToHom_toOrderHom]
  rfl

/-- Prepend the native zero-dimensional left block to the original simplex operator. -/
def prefixConeOperator (k n : ℕ) {d : SimplexCategory} (α : d ⟶ ⦋k + n + 1⦌) :
    (ordinalJoinLeft ⦋0⦌).obj d ⟶ ⦋k + 1 + n + 1⦌ :=
  (ordinalJoinLeft ⦋0⦌).map α ≫ (coneAmbientIso k n).hom

/-- The actual cone apex is the original successor vertex zero. -/
theorem prefixConeOperator_prefix_eval (k n : ℕ) {d : SimplexCategory}
    (α : d ⟶ ⦋k + n + 1⦌) (j : Fin 1) :
    ((prefixConeOperator k n α).toOrderHom
      ((AugmentedSimplexCategory.inl' ⦋0⦌ d).toOrderHom j)).val = 0 := by
  induction d using SimplexCategory.rec with | h d =>
    change ((coneAmbientIso k n).hom.toOrderHom
      (((ordinalJoinLeft ⦋0⦌).map α).toOrderHom
        ((AugmentedSimplexCategory.inl' ⦋0⦌ ⦋d⦌).toOrderHom j))).val = 0
    rw [coneAmbientIso_hom_eval, ← prefixIndex_eq_native, joinMap_prefix_eval]
    change j.val = 0
    have hj := j.isLt
    omega

/-- Every original vertex in the right block is shifted by exactly one. -/
theorem prefixConeOperator_suffix_eval (k n : ℕ) {d : SimplexCategory}
    (α : d ⟶ ⦋k + n + 1⦌) (j : Fin (d.len + 1)) :
    ((prefixConeOperator k n α).toOrderHom
      ((AugmentedSimplexCategory.inr' ⦋0⦌ d).toOrderHom j)).val =
      (α.toOrderHom j).val + 1 := by
  induction d using SimplexCategory.rec with | h d =>
    change ((coneAmbientIso k n).hom.toOrderHom
      (((ordinalJoinLeft ⦋0⦌).map α).toOrderHom
        ((AugmentedSimplexCategory.inr' ⦋0⦌ ⦋d⦌).toOrderHom j))).val = _
    rw [coneAmbientIso_hom_eval, ← suffixIndex_eq_native, joinMap_suffix_eval]
    change 0 + 1 + (α.toOrderHom j).val = (α.toOrderHom j).val + 1
    omega

/-- Prepending commutes with every actual operator on the original simplex domain. -/
theorem prefixConeOperator_precomp (k n : ℕ) {d e : SimplexCategory}
    (β : d ⟶ e) (α : e ⟶ ⦋k + n + 1⦌) :
    prefixConeOperator k n (β ≫ α) =
      (ordinalJoinLeft ⦋0⦌).map β ≫ prefixConeOperator k n α := by
  simp only [prefixConeOperator, Functor.map_comp, Category.assoc]

/-- Restriction to the original right block is the actual first-prefix coface. -/
theorem prefixConeOperator_suffix_comp (k n : ℕ) {d : SimplexCategory}
    (α : d ⟶ ⦋k + n + 1⦌) :
    AugmentedSimplexCategory.inr' ⦋0⦌ d ≫ prefixConeOperator k n α =
      α ≫ prefixDeleteFirstOperator k n := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext j
  apply Fin.ext
  change ((prefixConeOperator k n α).toOrderHom
    ((AugmentedSimplexCategory.inr' ⦋0⦌ d).toOrderHom j)).val =
      ((prefixDeleteFirstOperator k n).toOrderHom (α.toOrderHom j)).val
  rw [prefixConeOperator_suffix_eval, prefixDeleteFirstOperator_eval]

end DaggerOriginalPrefixBoundaryConeOperators
