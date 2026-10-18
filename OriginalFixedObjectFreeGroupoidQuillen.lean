import OriginalFixedObjectOrdinaryCellAdjunction
import OriginalFixedObjectStrictModel
import OriginalCofibrantBrownPreservationChallengeProof
import TopCatModelCategory.QuillenAdjunction

/-!
# The actual ordinary two-object free groupoid Quillen adjunction

Original Hom evaluation preserves fibrations and trivial fibrations by the exact
proved model classes. Native adjunction lifting supplies free-groupoid cofibrations.
Brown's existing statement applies to all simplicial inputs, which are cofibrant.
-/
set_option autoImplicit false
open CategoryTheory Limits HomotopicalAlgebra DaggerModels
open DaggerOriginalFixedObjectSimplicialCategories DaggerOriginalFixedObjectOrdinaryCellAdjunction
open scoped SSet.modelCategoryQuillen DaggerOriginalFixedObjectGroupoidClasses
  DaggerOriginalFixedObjectCofibrations DaggerOriginalFixedObjectStrictModel
universe u
namespace DaggerOriginalFixedObjectFreeGroupoidQuillen
noncomputable section

/-- The actual ordinary Hom evaluation preserves weak equivalences in the proved strict model. -/
theorem evaluation_weakEquivalence {C D : FixedStrictGroupoids TwoObjects}
    (F : C ⟶ D) [WeakEquivalence F] : WeakEquivalence (strictEvaluation.map F) :=
  (DaggerOriginalFixedObjectGroupoidClasses.strict_weakEquivalence_iff F).1 inferInstance
    TwoObjectDaggerGraph.left TwoObjectDaggerGraph.right

/-- The actual unchanged Hom evaluation preserves native fibrations. -/
theorem evaluation_fibration {C D : FixedStrictGroupoids TwoObjects}
    (F : C ⟶ D) [Fibration F] : Fibration (strictEvaluation.map F) :=
  (DaggerOriginalFixedObjectGroupoidClasses.strict_fibration_iff F).1 inferInstance
    TwoObjectDaggerGraph.left TwoObjectDaggerGraph.right

/-- Full ordinary Hom evaluation is a native trivial-fibration-preserving functor. -/
def evaluationPreservesTrivialFibrations : strictEvaluation.{u}.PreservesTrivialFibrations := by
  constructor
  intro C D F hF
  obtain ⟨hf, hw⟩ := (mem_trivialFibrations_iff F).1 hF
  have : Fibration F := hf
  have : WeakEquivalence F := hw
  exact (mem_trivialFibrations_iff _).2 ⟨evaluation_fibration F, evaluation_weakEquivalence F⟩

/-- Native adjunction lifting proves cofibration preservation by the actual free groupoid. -/
theorem freeGroupoid_cofibration {K L : SSet.{u}} (i : K ⟶ L) [Cofibration i] :
    Cofibration (freeGroupoid.map i) := by
  letI : strictEvaluation.PreservesTrivialFibrations := evaluationPreservesTrivialFibrations
  letI : freeGroupoid.PreservesCofibrations :=
    freeGroupoidAdjunction.preservesTrivialFibrations_iff_preservesCofibrations.1 inferInstance
  infer_instance

/-- The actual two-object free groupoid/evaluation adjunction is native Quillen. -/
theorem freeGroupoid_isQuillen : freeGroupoidAdjunction.{u}.IsQuillenAdjunction where
  cofibration_map i := freeGroupoid_cofibration i
  fibration_map p := evaluation_fibration p

/-- The actual ordinary free groupoid preserves trivial cofibrations. -/
theorem freeGroupoid_trivialCofibration {K L : SSet.{u}} (i : K ⟶ L)
    (hi : trivialCofibrations SSet.{u} i) :
    trivialCofibrations (FixedStrictGroupoids TwoObjects) (freeGroupoid.map i) := by
  letI : freeGroupoidAdjunction.IsQuillenAdjunction := freeGroupoid_isQuillen
  letI : freeGroupoid.PreservesTrivialCofibrations :=
    Adjunction.IsQuillenAdjunction.preservesTrivialCofibrations freeGroupoidAdjunction
  exact Functor.PreservesTrivialCofibrations.trivialCofibrations_le freeGroupoid i hi

/-- All simplicial inputs are cofibrant, so ordinary free groupoid preserves every weak map. -/
theorem freeGroupoid_weakEquivalence {K L : SSet.{u}} (f : K ⟶ L) [WeakEquivalence f] :
    WeakEquivalence (freeGroupoid.map f) := by
  apply DaggerOriginalCofibrantBrownPreservationChallengeProof.challengeProof
    SSet.{u} (FixedStrictGroupoids TwoObjects) freeGroupoid
    ?_ inferInstance inferInstance f inferInstance
  intro A B i hi hw
  exact ((mem_trivialCofibrations_iff _).1
    (freeGroupoid_trivialCofibration i ((mem_trivialCofibrations_iff _).2 ⟨hi, hw⟩))).2

end
end DaggerOriginalFixedObjectFreeGroupoidQuillen
