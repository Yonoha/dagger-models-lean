import NativeFibrantOppositeDerivability
import ActualQKanLocalizedComparison
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives

/-! Existence and fibrant evaluation of the original-Q right derived functor by native duality. -/

set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra Opposite
open DaggerOriginalCounitRightConeQRealizationAdjunction
open DaggerNativeFibrantOppositeDerivability
open scoped SSet.modelCategoryQuillen
universe u v w

namespace DaggerActualQDualFibrantDerived
noncomputable section

/-- The target weak class is exactly Mathlib's opposite weak class, used twice. -/
abbrev doubleWeak : MorphismProperty SSet.{u}ᵒᵖᵒᵖ := (weakEquivalences SSet.{u}ᵒᵖ).op

variable {H : Type w} [Category.{v} H] (L : SSet.{u} ⥤ H)
  [L.IsLocalization (weakEquivalences SSet.{u})]

/-- The literal original singular functor, transported through the native double-op equivalence. -/
def localizedSingular : SSet.{u}ᵒᵖᵒᵖ ⥤ H :=
  (opOpEquivalence SSet.{u}).functor ⋙ singular.{u} ⋙ L

/-- Its restriction to opposite cofibrant objects inverts every original weak map. -/
theorem dualFibrantInclusion_derives :
    (dualFibrantInclusion SSet.{u}).Derives (localizedSingular L) := by
  intro X Y f hf
  have : WeakEquivalence f.unop := ⟨hf⟩
  have : IsFibrant X.unop.obj.unop := isFibrant_unop X.unop.obj
  have : IsFibrant Y.unop.obj.unop := isFibrant_unop Y.unop.obj
  change IsIso (L.map (singular.map f.unop.hom.unop))
  apply Localization.inverts L (weakEquivalences SSet.{u})
  rw [← weakEquivalence_iff]
  exact DaggerActualQSingularFibrantWeakEquivalences.singular_weakEquivalence f.unop.hom.unop

/-- Native derivability gives a pointwise right derived functor; no existence premise is supplied. -/
theorem hasPointwiseRightDerivedFunctor :
    (localizedSingular L).HasPointwiseRightDerivedFunctor doubleWeak.{u} := by
  have := dualFibrantInclusion_isRightDerivabilityStructure SSet.{u}
  exact (dualFibrantInclusion_derives L).hasPointwiseRightDerivedFunctor

/-- Use Mathlib's total derived functor with the proved existence instance. -/
def rightDerived : doubleWeak.{u}.Localization ⥤ H :=
  have := hasPointwiseRightDerivedFunctor L
  have := (localizedSingular L).hasRightDerivedFunctor_of_hasPointwiseRightDerivedFunctor
  (localizedSingular L).totalRightDerived doubleWeak.Q doubleWeak

/-- The canonical comparison is the unchanged native total-derived unit. -/
def rightDerivedUnit : localizedSingular L ⟶ doubleWeak.Q ⋙ rightDerived L :=
  have := hasPointwiseRightDerivedFunctor L
  have := (localizedSingular L).hasRightDerivedFunctor_of_hasPointwiseRightDerivedFunctor
  (localizedSingular L).totalRightDerivedUnit doubleWeak.Q doubleWeak

/-- The resulting functor satisfies the universal property on the whole model category. -/
theorem rightDerived_isRightDerivedFunctor :
    (rightDerived L).IsRightDerivedFunctor (rightDerivedUnit L) doubleWeak.{u} := by
  unfold rightDerived rightDerivedUnit
  infer_instance

/-- The native right derived functor evaluates by an isomorphism at each fibrant object. -/
theorem rightDerivedUnit_isIso (X : (CofibrantObject SSet.{u}ᵒᵖ)ᵒᵖ) :
    IsIso ((rightDerivedUnit L).app ((dualFibrantInclusion SSet.{u}).functor.obj X)) := by
  have := hasPointwiseRightDerivedFunctor L
  have := (localizedSingular L).hasRightDerivedFunctor_of_hasPointwiseRightDerivedFunctor
  have := dualFibrantInclusion_isRightDerivabilityStructure SSet.{u}
  have := rightDerived_isRightDerivedFunctor L
  exact (dualFibrantInclusion_derives L).isIso (rightDerivedUnit L) X

end
end DaggerActualQDualFibrantDerived
