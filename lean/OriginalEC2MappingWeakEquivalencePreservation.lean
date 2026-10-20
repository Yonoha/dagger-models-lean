import OriginalEC2MappingFibrationPreservation
import OriginalFibrantBrownPreservationChallengeProof

/-!
# Weak-equivalence preservation by the literal original EC₂ mapping space

Every action of the original discrete C₂ on a TopCat space is jointly
continuous. The literal original compact-open mapping functor thus applies to
all objects of the proved Borel model category. Its trivial-fibration
preservation, and the native fibrant Brown factorization, prove preservation
of every original Borel weak equivalence. No preservation hypothesis for the
mapping functor is introduced.
-/

set_option autoImplicit false

open CategoryTheory HomotopicalAlgebra
open scoped TopCat.modelCategory DaggerOriginalBorelModelCategory
open DaggerOriginalDaggerRealizationC2Action DaggerOriginalDaggerRealizationContinuousAction
open DaggerOriginalEC2HomotopyFixedPointFunctor DaggerOriginalEC2MappingFibrationPreservation
open DaggerOriginalBorelModelConsequences DaggerOriginalEC2MappingCompactGeneration

universe u

namespace DaggerOriginalEC2MappingWeakEquivalencePreservation

noncomputable section

/-- Every original discrete C₂ action is jointly continuous on its original TopCat space. -/
theorem action_isContinuous (X : Action TopCat.{u} C2.{u}) : X.IsContinuous := by
  rw [Action.isContinuous_def]
  apply continuous_prod_of_discrete_left.mpr
  intro g
  exact (X.ρ g).asHom.hom.continuous

/-- Bundle joint continuity without changing an original action or its morphism. -/
def continuousActions : Action TopCat.{u} C2.{u} ⥤ ContAction TopCat.{u} C2.{u} :=
  ObjectProperty.lift _ (𝟭 _) action_isContinuous

/-- The original compact-open mapping functor on the actual Borel model category. -/
def originalMappingActionFunctor : Action TopCat.{u} C2.{u} ⥤ TopCat.{u} :=
  continuousActions ⋙ mappingTopFunctor

/-- The actual mapping functor preserves original Borel fibrations. -/
theorem originalMappingActionFunctor_map_fibration {X Y : Action TopCat.{u} C2.{u}}
    (p : X ⟶ Y) [Fibration p] : Fibration (originalMappingActionFunctor.map p) := by
  have : Fibration (continuousActions.map p).hom := by
    change Fibration p
    infer_instance
  exact originalPostcompose_fibration (continuousActions.map p)

/-- The actual mapping functor preserves original Borel trivial fibrations. -/
theorem originalMappingActionFunctor_map_trivialFibration {X Y : Action TopCat.{u} C2.{u}}
    (p : X ⟶ Y) [Fibration p] [WeakEquivalence p] :
    trivialFibrations TopCat.{u} (originalMappingActionFunctor.map p) := by
  have : Fibration (continuousActions.map p).hom := by
    change Fibration p
    infer_instance
  have : WeakEquivalence (continuousActions.map p).hom := by
    change WeakEquivalence p
    infer_instance
  exact originalPostcompose_trivialFibration (continuousActions.map p)

/-- Native Brown factorization proves actual preservation of every original Borel weak map. -/
theorem originalMappingActionFunctor_map_weakEquivalence {X Y : Action TopCat.{u} C2.{u}}
    (p : X ⟶ Y) [WeakEquivalence p] : WeakEquivalence (originalMappingActionFunctor.map p) := by
  exact DaggerOriginalFibrantBrownPreservationChallengeProof.challengeProof
    (Action TopCat.{u} C2.{u}) TopCat.{u} originalMappingActionFunctor (by
      intro A B f hf hw
      have : Fibration f := hf
      have : WeakEquivalence f := hw
      exact ((mem_trivialFibrations_iff _).1
        (originalMappingActionFunctor_map_trivialFibration f)).2)
    (everyAction_isFibrant X) (everyAction_isFibrant Y) p inferInstance

/-- Literal postcomposition preserves every input Borel weak equivalence. -/
theorem originalPostcompose_weakEquivalence {X Y : ContAction TopCat.{u} C2.{u}}
    (p : X ⟶ Y) [WeakEquivalence p.hom] : WeakEquivalence (postcompose p) :=
  originalMappingActionFunctor_map_weakEquivalence p.hom

/-- The manuscript's exact compact-generated mapping arrow preserves the same weak equivalences. -/
theorem compactPostcompose_weakEquivalence {X Y : ContAction TopCat.{u} C2.{u}}
    (p : X ⟶ Y) [WeakEquivalence p.hom] :
    WeakEquivalence (compactMappingTopFunctor.map p) :=
  (compact_postcompose_weakEquivalence_iff p).2 (originalPostcompose_weakEquivalence p)

end

end DaggerOriginalEC2MappingWeakEquivalencePreservation
