import OriginalSimplicialParameterActionCofibrations
import OriginalSimplicialEquivariantEnrichedAdjunction
import OriginalEC2SimplicialProjectiveCofibrancy
import OriginalFibrantBrownPreservationChallengeProof
import TopCatModelCategory.QuillenAdjunction

/-!
# The original enriched Map right Quillen functor for simplicial C₂ actions

For every projectively cofibrant original action E, the literal product-enriched adjunction
is Quillen from simplicial sets to the projective model on the original simplicial actions.
Original boundary and horn parameter products prove preservation of fibrations and trivial
fibrations. The independent fibrant Brown theorem then proves weak-equivalence preservation
between projectively fibrant targets. Apply these results to the actual Ebullet C₂, whose
projective cofibrancy was proved from its original equivariant skeletal cell complex.
-/

set_option autoImplicit false

open CategoryTheory HomotopicalAlgebra
open DaggerOriginalDaggerRealizationC2Action DaggerOriginalEC2SimplicialAction
open DaggerOriginalSimplicialEquivariantParameterTensor
open DaggerOriginalSimplicialEquivariantEnrichedAdjunction
open DaggerOriginalSimplicialParameterActionCofibrations
open scoped SSet.modelCategoryQuillen DaggerOriginalSimplicialActionModelCategory

universe u

namespace DaggerOriginalSimplicialEquivariantEnrichedQuillen

noncomputable section

/-- The same original enriched Map preserves every projective fibration. -/
theorem enrichedMapping_map_fibration (E : Action SSet.{u} C2.{u}) [IsCofibrant E]
    {X Y : Action SSet.{u} C2.{u}} (p : X ⟶ Y) [Fibration p] :
    Fibration ((enrichedMappingFunctor E).map p) := by
  rw [fibration_iff, SSet.modelCategoryQuillen.fibrations_eq]
  intro A B i hi
  simp only [SSet.modelCategoryQuillen.J, MorphismProperty.iSup_iff] at hi
  obtain ⟨n, ⟨i⟩⟩ := hi
  apply ((enrichedAdjunction E).hasLiftingProperty_iff _ p).1
  obtain ⟨hc, hw⟩ := (mem_trivialCofibrations_iff _).1
    (simplicialParameterTensorMap_horn_trivialCofibration n i E)
  have : Cofibration ((parameterTensorFunctor E).map (SSet.horn (n + 1) i).ι) := hc
  have : WeakEquivalence ((parameterTensorFunctor E).map (SSet.horn (n + 1) i).ι) := hw
  infer_instance

/-- The same original enriched Map preserves every projective trivial fibration. -/
theorem enrichedMapping_map_trivialFibration (E : Action SSet.{u} C2.{u}) [IsCofibrant E]
    {X Y : Action SSet.{u} C2.{u}} (p : X ⟶ Y) [Fibration p] [WeakEquivalence p] :
    trivialFibrations SSet.{u} ((enrichedMappingFunctor E).map p) := by
  rw [← SSet.modelCategoryQuillen.rlp_I_eq_trivialFibrations]
  rintro _ _ _ ⟨n⟩
  apply ((enrichedAdjunction E).hasLiftingProperty_iff _ p).1
  have : Cofibration ((parameterTensorFunctor E).map (SSet.boundary n).ι) :=
    simplicialParameterTensorMap_cofibration (SSet.boundary n) E
  infer_instance

/-- Native fibration preservation is registered for the literal enriched functor. -/
instance enrichedMapping_preservesFibrations (E : Action SSet.{u} C2.{u}) [IsCofibrant E] :
    (enrichedMappingFunctor E).PreservesFibrations where
  fibration_map p := enrichedMapping_map_fibration E p

/-- Native trivial-fibration preservation is registered for the literal enriched functor. -/
instance enrichedMapping_preservesTrivialFibrations (E : Action SSet.{u} C2.{u})
    [IsCofibrant E] : (enrichedMappingFunctor E).PreservesTrivialFibrations where
  trivialFibrations_le := by
    intro X Y p hp
    obtain ⟨hf, hw⟩ := (mem_trivialFibrations_iff _).1 hp
    have : Fibration p := hf
    have : WeakEquivalence p := hw
    exact enrichedMapping_map_trivialFibration E p

/-- The same actual product tensor preserves all native simplicial cofibrations. -/
theorem parameterTensor_map_cofibration (E : Action SSet.{u} C2.{u}) [IsCofibrant E]
    {A B : SSet.{u}} (i : A ⟶ B) [Cofibration i] :
    Cofibration ((parameterTensorFunctor E).map i) := by
  have : (parameterTensorFunctor E).PreservesCofibrations :=
    (enrichedAdjunction E).preservesTrivialFibrations_iff_preservesCofibrations.1 inferInstance
  infer_instance

/-- The original product tensor and enriched Map form a Quillen adjunction. -/
theorem enrichedAdjunction_isQuillen (E : Action SSet.{u} C2.{u}) [IsCofibrant E] :
    (enrichedAdjunction E).IsQuillenAdjunction where
  cofibration_map i := parameterTensor_map_cofibration E i
  fibration_map p := enrichedMapping_map_fibration E p

/-- Original enriched Map preserves weak equivalences between projectively fibrant targets. -/
theorem enrichedMapping_map_weakEquivalence (E : Action SSet.{u} C2.{u}) [IsCofibrant E]
    {X Y : Action SSet.{u} C2.{u}} [IsFibrant X] [IsFibrant Y]
    (p : X ⟶ Y) [WeakEquivalence p] :
    WeakEquivalence ((enrichedMappingFunctor E).map p) := by
  exact DaggerOriginalFibrantBrownPreservationChallengeProof.challengeProof
    (Action SSet.{u} C2.{u}) SSet.{u} (enrichedMappingFunctor E) (by
      intro A B f hf hw
      have : Fibration f := hf
      have : WeakEquivalence f := hw
      exact ((mem_trivialFibrations_iff _).1 (enrichedMapping_map_trivialFibration E f)).2)
    (inferInstance : IsFibrant X) (inferInstance : IsFibrant Y) p inferInstance

/-- The literal original Ebullet C₂ enriched tensor adjunction is projectively Quillen. -/
theorem originalEC2_enrichedAdjunction_isQuillen :
    (enrichedAdjunction simplicialAction.{u}).IsQuillenAdjunction :=
  enrichedAdjunction_isQuillen simplicialAction

/-- The literal Ebullet C₂ enriched Map preserves the same fibrant-target weak equivalences. -/
theorem originalEC2_enrichedMapping_map_weakEquivalence
    {X Y : Action SSet.{u} C2.{u}} [IsFibrant X] [IsFibrant Y]
    (p : X ⟶ Y) [WeakEquivalence p] :
    WeakEquivalence ((enrichedMappingFunctor simplicialAction).map p) :=
  enrichedMapping_map_weakEquivalence simplicialAction p

end

end DaggerOriginalSimplicialEquivariantEnrichedQuillen
