import FullWeakSmithGeneratorBridge
import OriginalWholeWeakSolutionSets
import NativeJoyalTrivialRecognition

/-! A literal small ordinary boundary-based Smith family in the unchanged full weak class. -/
set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra
open DaggerNativeJoyalMappingTest DaggerNativeJoyalFirstFactorization
open DaggerNativeBoundaryJoyalMappingWeak
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeFullWeakSmithGenerators
noncomputable section

instance boundarySmall : MorphismProperty.IsSmall.{u} SSet.modelCategoryQuillen.I.{u} :=
  MorphismProperty.isSmall_ofHoms _

def solutions := DaggerOriginalWholeWeakSolutionSets.native SSet.modelCategoryQuillen.I.{u}
def generators : MorphismProperty SSet.{u} := DaggerSmithSolutionSet.J solutions.{u}

instance generatorsSmall : MorphismProperty.IsSmall.{u} generators.{u} :=
  DaggerSmithSolutionSet.instIsSmallJ solutions

theorem boundary_rlp_weak :
    SSet.modelCategoryQuillen.I.{u}.rlp ≤ weakCategoricalEquivalences := by
  intro A B f hf
  exact DaggerNativeBoundaryJoyalMappingWeak.boundary_rlp_weak f
    (fun n ↦ hf (SSet.boundary n).ι ⟨n⟩)

theorem boundary_cof : SSet.modelCategoryQuillen.I.{u}.rlp.llp =
    MorphismProperty.monomorphisms SSet.{u} := by
  rw [SSet.modelCategoryQuillen.rlp_I_eq_trivialFibrations, trivialFibrations_llp]
  ext A B f
  exact (cofibration_iff f).symm.trans (SSet.modelCategoryQuillen.cofibration_iff f)

theorem generators_le : generators.{u} ≤
    MorphismProperty.monomorphisms SSet.{u} ⊓ weakCategoricalEquivalences := by
  simpa only [boundary_cof] using
    DaggerFullWeakSmithGeneratorBridge.generators_le solutions boundary_rlp_weak

theorem weak_right_eq : generators.{u}.rlp ⊓ weakCategoricalEquivalences =
    (MorphismProperty.monomorphisms SSet.{u}).rlp := by
  rw [← boundary_cof, MorphismProperty.rlp_llp_rlp]
  exact DaggerFullWeakSmithGeneratorBridge.weak_right_eq solutions boundary_rlp_weak

theorem full_candidate_le : candidateFibrations.{u} ≤ generators.{u}.rlp :=
  MorphismProperty.antitone_rlp generators_le

theorem generated_left_le : generators.{u}.rlp.llp ≤ MorphismProperty.monomorphisms SSet.{u} := by
  simpa only [boundary_cof] using
    DaggerFullWeakSmithGeneratorBridge.generated_left_le solutions boundary_rlp_weak

def generatedFactorization :
    generators.{u}.rlp.llp.FunctorialFactorizationData generators.{u}.rlp :=
  DaggerFullWeakSmithGeneratorBridge.generatedFactorization solutions

end
end DaggerNativeFullWeakSmithGenerators
