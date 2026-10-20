import OriginalEC2ProductBorelCofibrations
import OriginalEC2MappingFibrationRecognition

/-!
# Actual fibration preservation by the original EC₂ mapping space

The literal original boundary products are Borel cofibrations, and the horn
products are Borel trivial cofibrations. The already proved original lifting
correspondence therefore proves preservation of fibrations and trivial
fibrations by the original compact-open mapping arrow and its exact
compact-generated counterpart.
-/

set_option autoImplicit false

open CategoryTheory HomotopicalAlgebra
open scoped TopCat.modelCategory DaggerOriginalBorelModelCategory
open DaggerOriginalDaggerRealizationC2Action DaggerOriginalEC2HomotopyFixedPointFunctor
open DaggerOriginalEC2ProductBorelCofibrations DaggerOriginalEC2MappingFibrationRecognition
open DaggerOriginalEC2MappingCompactGeneration

universe u

namespace DaggerOriginalEC2MappingFibrationPreservation

noncomputable section

/-- The original compact-open mapping arrow preserves input Borel fibrations. -/
theorem originalPostcompose_fibration {X Y : ContAction TopCat.{u} C2.{u}}
    (p : X ⟶ Y) [Fibration p.hom] : Fibration (postcompose p) := by
  apply (originalPostcompose_fibration_iff p).2
  intro n i
  obtain ⟨hf, hw⟩ := (mem_trivialCofibrations_iff _).1
    (actualEC2HornProduct_borelTrivialCofibration n i)
  have : Cofibration _ := hf
  have : WeakEquivalence _ := hw
  exact inferInstance

/-- The original compact-open mapping arrow preserves input Borel trivial fibrations. -/
theorem originalPostcompose_trivialFibration {X Y : ContAction TopCat.{u} C2.{u}}
    (p : X ⟶ Y) [Fibration p.hom] [WeakEquivalence p.hom] :
    trivialFibrations TopCat.{u} (postcompose p) := by
  apply (mem_trivialFibrations_iff _).2
  apply (originalPostcompose_trivialFibration_iff p).2
  intro n
  have := actualEC2BoundaryProduct_borelCofibration.{u} n
  exact inferInstance

/-- Compact generation retains actual preservation of input Borel fibrations. -/
theorem compactPostcompose_fibration {X Y : ContAction TopCat.{u} C2.{u}}
    (p : X ⟶ Y) [Fibration p.hom] : Fibration (compactMappingTopFunctor.map p) :=
  (compact_postcompose_fibration_iff p).2 (originalPostcompose_fibration p)

/-- Compact generation retains actual preservation of input Borel trivial fibrations. -/
theorem compactPostcompose_trivialFibration {X Y : ContAction TopCat.{u} C2.{u}}
    (p : X ⟶ Y) [Fibration p.hom] [WeakEquivalence p.hom] :
    trivialFibrations TopCat.{u} (compactMappingTopFunctor.map p) := by
  obtain ⟨hf, hw⟩ := (mem_trivialFibrations_iff _).1
    (originalPostcompose_trivialFibration p)
  exact (mem_trivialFibrations_iff _).2
    ⟨compactPostcompose_fibration p, (compact_postcompose_weakEquivalence_iff p).2 hw⟩

end

end DaggerOriginalEC2MappingFibrationPreservation
