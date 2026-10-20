import ChallengeActualQDerivedCounit
import ActualQOriginalCounitLocalization
import ProofActualQSingularWeakReflection

set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra Opposite
open DaggerNativeFibrantOppositeDerivability DaggerActualQDualFibrantDerived
open scoped SSet.modelCategoryQuillen
universe u

namespace DaggerActualQDerivedCounitChallenge

theorem verified : statement.{u} := by
  constructor
  · intro X hX
    have : X.KanComplex := hX
    exact DaggerActualQOriginalCounitLocalization.counit_localized_isIso
      (weakEquivalences SSet.{u}).Q X
  · let L := (weakEquivalences SSet.{u}).Q
    refine ⟨rightDerived L, rightDerivedUnit L, rightDerived_isRightDerivedFunctor L,
      DaggerActualQDerivedEquivalence.rightDerived_isEquivalence L, ?_⟩
    intro X hX
    have : X.KanComplex := hX
    have : IsCofibrant (op X) := (isCofibrant_op_iff_isFibrant X).mpr inferInstance
    exact rightDerivedUnit_isIso L (op (CofibrantObject.mk (op X)))

end DaggerActualQDerivedCounitChallenge
