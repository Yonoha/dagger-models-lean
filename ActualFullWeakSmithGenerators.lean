import FullWeakSmithGeneratorBridge
import OriginalNormalGeneratorWholeSolutions
import ActualAntiJoyalFirstFactorization

/-! Original normal generators give full weak Smith generators and exact right recognition. -/
set_option autoImplicit false
open CategoryTheory DaggerModels
open DaggerModels.OriginalAntiInvolutiveNormalMonoSaturation
open DaggerActualAntiNormalFactorization DaggerActualAntiNormalBoundaryLifting
open DaggerActualAntiJoyalMappingWeakProperties DaggerActualAntiJoyalFirstFactorization
universe u
namespace DaggerActualFullWeakSmithGenerators
noncomputable section

def generators : MorphismProperty AntiInvolutiveSSet.{u} :=
  DaggerSmithSolutionSet.J DaggerOriginalNormalGeneratorWholeSolutions.actual.{u}

instance generatorsSmall : MorphismProperty.IsSmall.{u} generators.{u} :=
  DaggerSmithSolutionSet.instIsSmallJ DaggerOriginalNormalGeneratorWholeSolutions.actual

theorem generators_rlp_weak : normalGeneratingCofibrations.{u}.rlp ≤ weakEquivalences := by
  rw [← normalMonos_rlp_eq_generators_rlp]
  exact normal_rlp_le_weak

theorem generators_le : generators.{u} ≤ normalMonos.{u} ⊓ weakEquivalences := by
  rw [normalMonos_eq_generators_rlp_llp]
  exact DaggerFullWeakSmithGeneratorBridge.generators_le
    DaggerOriginalNormalGeneratorWholeSolutions.actual generators_rlp_weak

theorem weak_right_eq : generators.{u}.rlp ⊓ weakEquivalences = normalMonos.{u}.rlp := by
  rw [normalMonos_rlp_eq_generators_rlp]
  exact DaggerFullWeakSmithGeneratorBridge.weak_right_eq
    DaggerOriginalNormalGeneratorWholeSolutions.actual generators_rlp_weak

theorem full_candidate_le : candidateFibrations.{u} ≤ generators.{u}.rlp :=
  MorphismProperty.antitone_rlp generators_le

theorem generated_left_le : generators.{u}.rlp.llp ≤ normalMonos.{u} := by
  rw [normalMonos_eq_generators_rlp_llp]
  exact DaggerFullWeakSmithGeneratorBridge.generated_left_le
    DaggerOriginalNormalGeneratorWholeSolutions.actual generators_rlp_weak

def generatedFactorization :
    generators.{u}.rlp.llp.FunctorialFactorizationData generators.{u}.rlp :=
  DaggerFullWeakSmithGeneratorBridge.generatedFactorization
    DaggerOriginalNormalGeneratorWholeSolutions.actual

end
end DaggerActualFullWeakSmithGenerators
