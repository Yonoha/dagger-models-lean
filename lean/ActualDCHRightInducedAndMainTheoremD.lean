import ActualOriginalCandidateCreation
import ActualTaggedNonQuillenForExactDCHClasses

/-! The constructed original DCH model and both actual non-Quillen tagged adjunctions. -/
set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra DaggerModels
open DaggerModels.OriginalTaggedReverseAdjunctions
open DaggerModels.OriginalAntiInvolutiveNormalMonoSaturation
open DaggerActualAntiNormalFactorization
open DaggerOriginalTaggedRightAdjunctionQuillenObstruction
universe u
namespace DaggerActualDCHRightInducedAndMainTheoremD
noncomputable section

def model : ModelCategory AntiInvolutiveSSet.{u} :=
  DaggerActualOriginalAntiJoyalSmithModelData.modelData.{u}.model

local instance actualDCH : ModelCategory AntiInvolutiveSSet.{u} := model.{u}
local instance daggerJoyal : ModelCategory DaggerSSet.{u} :=
  DaggerActualRigidificationQuillen.modelD.{u}

theorem cofibration_iff_normal {X Y : AntiInvolutiveSSet.{u}} (f : X ⟶ Y) :
    Cofibration f ↔ AntiInvolutiveSSet.NormalMono f := by
  rw [cofibration_iff]
  change CategoryWithCofibrations.cofibrations f ↔ AntiInvolutiveSSet.NormalMono f
  rw [DaggerActualOriginalAntiJoyalSmithModelData.modelData.modelCof,
    ← normalMonos_eq_generators_rlp_llp]

theorem weakEquivalence_iff_original {X Y : AntiInvolutiveSSet.{u}} (f : X ⟶ Y) :
    WeakEquivalence f ↔ DaggerActualAntiJoyalMappingWeakProperties.weakEquivalences f := by
  rw [weakEquivalence_iff]
  change CategoryWithWeakEquivalences.weakEquivalences f ↔
    DaggerActualAntiJoyalMappingWeakProperties.weakEquivalences f
  rw [DaggerActualOriginalAntiJoyalSmithModelData.modelData.modelWeak]

theorem fibration_iff_underlying_candidate {X Y : AntiInvolutiveSSet.{u}} (f : X ⟶ Y) :
    Fibration f ↔ DaggerNativeJoyalFirstFactorization.candidateFibrations f.hom := by
  rw [fibration_iff]
  change CategoryWithFibrations.fibrations f ↔
    DaggerNativeJoyalFirstFactorization.candidateFibrations f.hom
  rw [DaggerActualOriginalAntiJoyalSmithModelData.modelData.modelFib,
    ← normalMonos_eq_generators_rlp_llp]
  exact DaggerActualOriginalCandidateCreation.candidate_iff_underlying f

def ordinaryJoyalModel : ModelCategory SSet.{u} :=
  DaggerNativeOriginalJoyalSmithModelData.modelData.{u}.model

local instance ordinaryJoyal : ModelCategory SSet.{u} := ordinaryJoyalModel.{u}
local instance ordinaryWeak : CategoryWithWeakEquivalences SSet.{u} :=
  ordinaryJoyalModel.categoryWithWeakEquivalences
local instance ordinaryFibrations : CategoryWithFibrations SSet.{u} :=
  ordinaryJoyalModel.categoryWithFibrations
local instance ordinaryCofibrations : CategoryWithCofibrations SSet.{u} :=
  ordinaryJoyalModel.categoryWithCofibrations

theorem weakEquivalence_iff_underlying {X Y : AntiInvolutiveSSet.{u}} (f : X ⟶ Y) :
    WeakEquivalence f ↔ WeakEquivalence f.hom := by
  rw [weakEquivalence_iff_original, weakEquivalence_iff]
  change DaggerActualAntiJoyalMappingWeakProperties.weakEquivalences f ↔
    CategoryWithWeakEquivalences.weakEquivalences f.hom
  rw [DaggerNativeOriginalJoyalSmithModelData.modelData.modelWeak]
  rfl

theorem fibration_iff_underlying {X Y : AntiInvolutiveSSet.{u}} (f : X ⟶ Y) :
    Fibration f ↔ Fibration f.hom := by
  rw [fibration_iff_underlying_candidate, fibration_iff]
  change DaggerNativeJoyalFirstFactorization.candidateFibrations f.hom ↔
    CategoryWithFibrations.fibrations f.hom
  rw [DaggerNativeOriginalJoyalSmithModelData.modelData.modelFib,
    DaggerNativeFullWeakSmithGenerators.boundary_cof]
  rfl

theorem both_not_quillen :
    ¬ leftAdjunction.{u}.IsQuillenAdjunction ∧ ¬ rightAdjunction.{u}.IsQuillenAdjunction :=
  DaggerActualTaggedNonQuillenForExactDCHClasses.both_not_quillen_for_exact_classes
    cofibration_iff_normal weakEquivalence_iff_original

theorem cofibrations_not_restriction :
    ¬ ∀ {X Y : DaggerSSet.{u}} (f : X ⟶ Y), Cofibration f ↔ Cofibration
      (DaggerModels.OriginalTaggedReversePresheafInclusion.presheafRoute.map f) := by
  intro h
  obtain ⟨hc, hn⟩ :=
    literal_freeZero_model_cofibration_mismatch
      DaggerActualTaggedObstructionsForStandardDaggerModel.dagger_cofibration_iff
      cofibration_iff_normal
  exact hn ((h DaggerOriginalTaggedFreeZeroNativeWitness.freeZeroArrow).mp hc)

end
end DaggerActualDCHRightInducedAndMainTheoremD
