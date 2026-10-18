import NativeOriginalSecondFactorization

/-! Full original ordinary Joyal Smith model data with every closure hypothesis discharged. -/
set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra
open DaggerNativeJoyalMappingTest DaggerNativeJoyalFirstFactorization
open DaggerNativeFullWeakSmithGenerators
universe u
namespace DaggerNativeOriginalJoyalSmithModelData
noncomputable section

def modelData : DaggerSmithSolutionSet.CombinatorialData solutions.{u} := by
  have : MorphismProperty.IsStableUnderCobaseChange
      (SSet.modelCategoryQuillen.I.{u}.rlp.llp ⊓ weakCategoricalEquivalences) := by
    simpa only [boundary_cof] using
      (inferInstance : MorphismProperty.IsStableUnderCobaseChange
        (MorphismProperty.monomorphisms SSet.{u} ⊓ weakCategoricalEquivalences))
  have : MorphismProperty.IsStableUnderTransfiniteComposition.{u}
      (SSet.modelCategoryQuillen.I.{u}.rlp.llp ⊓ weakCategoricalEquivalences) := by
    simpa only [boundary_cof] using
      (inferInstance : MorphismProperty.IsStableUnderTransfiniteComposition.{u}
        (MorphismProperty.monomorphisms SSet.{u} ⊓ weakCategoricalEquivalences))
  exact DaggerSmithSolutionSet.combinatorialData solutions boundary_rlp_weak

theorem generated_left_eq : generators.{u}.rlp.llp =
    MorphismProperty.monomorphisms SSet.{u} ⊓ weakCategoricalEquivalences := by
  simpa only [boundary_cof] using modelData.{u}.trivialCofibrations

theorem generated_right_eq : generators.{u}.rlp = candidateFibrations.{u} := by
  simpa only [boundary_cof, candidateFibrations] using modelData.{u}.fibrations

end
end DaggerNativeOriginalJoyalSmithModelData
