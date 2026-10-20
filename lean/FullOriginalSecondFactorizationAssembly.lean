import NativeFullWeakSmithGenerators
import ActualFullWeakSmithGenerators

/-!
# Exact original second factorizations once the two remaining closure instances are proved

The original weak predicates and full right candidates are literal in both outputs.
Cobase and transfinite closure are explicit hypotheses, not asserted instances.
-/
set_option autoImplicit false
open CategoryTheory DaggerModels
open DaggerNativeJoyalMappingTest DaggerActualAntiJoyalMappingWeakProperties
open DaggerModels.OriginalAntiInvolutiveNormalMonoSaturation
universe u
namespace DaggerFullOriginalSecondFactorizationAssembly
noncomputable section

section Native
variable [MorphismProperty.IsStableUnderCobaseChange
    (MorphismProperty.monomorphisms SSet.{u} ⊓ weakCategoricalEquivalences)]
  [MorphismProperty.IsStableUnderTransfiniteComposition.{u}
    (MorphismProperty.monomorphisms SSet.{u} ⊓ weakCategoricalEquivalences)]

def native : MorphismProperty.FunctorialFactorizationData
    (MorphismProperty.monomorphisms SSet.{u} ⊓ weakCategoricalEquivalences)
    DaggerNativeJoyalFirstFactorization.candidateFibrations.{u} := by
  have : MorphismProperty.IsStableUnderCobaseChange
      ((SSet.modelCategoryQuillen.I.{u}).rlp.llp ⊓ weakCategoricalEquivalences) := by
    simpa only [DaggerNativeFullWeakSmithGenerators.boundary_cof] using
      (inferInstance : MorphismProperty.IsStableUnderCobaseChange
        (MorphismProperty.monomorphisms SSet.{u} ⊓ weakCategoricalEquivalences))
  have : MorphismProperty.IsStableUnderTransfiniteComposition.{u}
      ((SSet.modelCategoryQuillen.I.{u}).rlp.llp ⊓ weakCategoricalEquivalences) := by
    simpa only [DaggerNativeFullWeakSmithGenerators.boundary_cof] using
      (inferInstance : MorphismProperty.IsStableUnderTransfiniteComposition.{u}
        (MorphismProperty.monomorphisms SSet.{u} ⊓ weakCategoricalEquivalences))
  simpa only [DaggerNativeFullWeakSmithGenerators.boundary_cof] using
    DaggerSmithSolutionSet.trivialCofibrationFactorization
      DaggerNativeFullWeakSmithGenerators.solutions
      DaggerNativeFullWeakSmithGenerators.boundary_rlp_weak
end Native

section Actual
variable [(normalMonos.{u} ⊓ weakEquivalences).IsStableUnderCobaseChange]
  [MorphismProperty.IsStableUnderTransfiniteComposition.{u} (normalMonos.{u} ⊓ weakEquivalences)]

def actual : (normalMonos.{u} ⊓ weakEquivalences).FunctorialFactorizationData
    DaggerActualAntiJoyalFirstFactorization.candidateFibrations.{u} := by
  have : MorphismProperty.IsStableUnderCobaseChange
      (normalGeneratingCofibrations.{u}.rlp.llp ⊓ weakEquivalences) := by
    simpa only [← DaggerActualAntiNormalFactorization.normalMonos_eq_generators_rlp_llp] using
      (inferInstance : (normalMonos.{u} ⊓ weakEquivalences).IsStableUnderCobaseChange)
  have : MorphismProperty.IsStableUnderTransfiniteComposition.{u}
      (normalGeneratingCofibrations.{u}.rlp.llp ⊓ weakEquivalences) := by
    simpa only [← DaggerActualAntiNormalFactorization.normalMonos_eq_generators_rlp_llp] using
      (inferInstance : MorphismProperty.IsStableUnderTransfiniteComposition.{u}
        (normalMonos.{u} ⊓ weakEquivalences))
  simpa only [← DaggerActualAntiNormalFactorization.normalMonos_eq_generators_rlp_llp] using
    DaggerSmithSolutionSet.trivialCofibrationFactorization
      DaggerOriginalNormalGeneratorWholeSolutions.actual
      DaggerActualFullWeakSmithGenerators.generators_rlp_weak
end Actual

end
end DaggerFullOriginalSecondFactorizationAssembly
