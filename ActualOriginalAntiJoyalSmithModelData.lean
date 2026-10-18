import ActualOriginalAntiWeakNormalClosure

/-! Unconditional factorization and Smith model data for original anti-involutive maps. -/
set_option autoImplicit false
open CategoryTheory DaggerModels
open DaggerModels.OriginalAntiInvolutiveNormalMonoSaturation
open DaggerActualAntiJoyalMappingWeakProperties DaggerActualAntiNormalFactorization
universe u
namespace DaggerActualOriginalAntiJoyalSmithModelData
noncomputable section

def secondFactorization : (normalMonos.{u} ⊓ weakEquivalences).FunctorialFactorizationData
    DaggerActualAntiJoyalFirstFactorization.candidateFibrations.{u} :=
  DaggerFullOriginalSecondFactorizationAssembly.actual

instance hasSecondFactorization : MorphismProperty.HasFunctorialFactorization
    (normalMonos.{u} ⊓ weakEquivalences)
    DaggerActualAntiJoyalFirstFactorization.candidateFibrations.{u} := ⟨⟨secondFactorization⟩⟩

def modelData : DaggerSmithSolutionSet.CombinatorialData
    DaggerOriginalNormalGeneratorWholeSolutions.actual.{u} := by
  have : MorphismProperty.IsStableUnderCobaseChange
      (normalGeneratingCofibrations.{u}.rlp.llp ⊓ weakEquivalences) := by
    simpa only [← normalMonos_eq_generators_rlp_llp] using
      (inferInstance : (normalMonos.{u} ⊓ weakEquivalences).IsStableUnderCobaseChange)
  have : MorphismProperty.IsStableUnderTransfiniteComposition.{u}
      (normalGeneratingCofibrations.{u}.rlp.llp ⊓ weakEquivalences) := by
    simpa only [← normalMonos_eq_generators_rlp_llp] using
      (inferInstance : MorphismProperty.IsStableUnderTransfiniteComposition.{u}
        (normalMonos.{u} ⊓ weakEquivalences))
  exact DaggerSmithSolutionSet.combinatorialData
    DaggerOriginalNormalGeneratorWholeSolutions.actual
    DaggerActualFullWeakSmithGenerators.generators_rlp_weak

theorem generated_left_eq : DaggerActualFullWeakSmithGenerators.generators.{u}.rlp.llp =
    normalMonos.{u} ⊓ weakEquivalences := by
  simpa only [← normalMonos_eq_generators_rlp_llp] using modelData.{u}.trivialCofibrations

theorem generated_right_eq : DaggerActualFullWeakSmithGenerators.generators.{u}.rlp =
    DaggerActualAntiJoyalFirstFactorization.candidateFibrations.{u} := by
  simpa only [← normalMonos_eq_generators_rlp_llp,
    DaggerActualAntiJoyalFirstFactorization.candidateFibrations] using modelData.{u}.fibrations

end
end DaggerActualOriginalAntiJoyalSmithModelData
