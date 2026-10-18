import OriginalFixedObjectAmbientDaggerModel
import OriginalFixedObjectStrictDaggerModel

/-!
# The actual original dagger completion/inclusion Quillen adjunction

Both original ambient and strict fixed-object models have been proved. Inclusion
retains every full original Hom map, so it preserves and detects fibrations and weak
equivalences. The actual full completion/inclusion adjunction therefore preserves
cofibrations and is native Quillen. No Quillen equivalence or simplicial model claim.
-/
set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra
open DaggerOriginalFixedObjectDaggerCategories DaggerOriginalFixedObjectGroupoidCompletionAdjunction
open scoped DaggerOriginalFixedObjectGroupoidClasses DaggerOriginalFixedObjectCofibrations
  DaggerOriginalFixedObjectStrictDaggerModel DaggerOriginalFixedObjectAmbientDaggerModel
universe u
namespace DaggerOriginalFixedObjectDaggerCompletionQuillen
noncomputable section

/-- Inclusion preserves and detects the exact original Homwise weak-equivalence class. -/
theorem inclusion_weakEquivalence_iff {O : Type u}
    {C D : FixedStrictDaggerGroupoids O} (F : C ⟶ D) :
    WeakEquivalence ((fixedDaggerInclusion O).map F) ↔ WeakEquivalence F := by
  rw [DaggerOriginalFixedObjectAmbientDaggerModel.weakEquivalence_iff_original,
    DaggerOriginalFixedObjectGroupoidClasses.strictDagger_weakEquivalence_iff]
  rfl

/-- Inclusion preserves and detects the exact original Homwise fibration class. -/
theorem inclusion_fibration_iff {O : Type u} {C D : FixedStrictDaggerGroupoids O} (F : C ⟶ D) :
    Fibration ((fixedDaggerInclusion O).map F) ↔ Fibration F := by
  rw [DaggerOriginalFixedObjectAmbientDaggerModel.fibration_iff_original,
    DaggerOriginalFixedObjectGroupoidClasses.strictDagger_fibration_iff]
  rfl

/-- Inclusion preserves and detects the full original trivial-fibration class. -/
theorem inclusion_trivialFibration_iff {O : Type u}
    {C D : FixedStrictDaggerGroupoids O} (F : C ⟶ D) :
    trivialFibrations (FixedDaggerCategory O) ((fixedDaggerInclusion O).map F) ↔
      trivialFibrations (FixedStrictDaggerGroupoids O) F := by
  rw [mem_trivialFibrations_iff, mem_trivialFibrations_iff,
    inclusion_fibration_iff, inclusion_weakEquivalence_iff]

/-- The actual unchanged original inclusion is a native trivial-fibration-preserving functor. -/
def inclusionPreservesTrivialFibrations (O : Type u) :
    (fixedDaggerInclusion O).PreservesTrivialFibrations := by
  constructor
  intro C D F hF
  exact (inclusion_trivialFibration_iff F).2 hF

/-- Native adjunction lifting makes the full original completion preserve cofibrations. -/
theorem completion_cofibration {O : Type u} {C D : FixedDaggerCategory O}
    (F : C ⟶ D) [Cofibration F] : Cofibration ((fixedDaggerCompletion O).map F) := by
  letI : (fixedDaggerInclusion O).PreservesTrivialFibrations :=
    inclusionPreservesTrivialFibrations O
  let adj := fixedDaggerCompletionInclusionAdjunction O
  letI : (fixedDaggerCompletion O).PreservesCofibrations :=
    adj.preservesTrivialFibrations_iff_preservesCofibrations.1 inferInstance
  infer_instance

/-- The actual full original completion/inclusion adjunction is native Quillen. -/
theorem completionInclusion_isQuillen (O : Type u) :
    (fixedDaggerCompletionInclusionAdjunction O).IsQuillenAdjunction where
  cofibration_map i := completion_cofibration i
  fibration_map p := by
    intro hp
    exact (inclusion_fibration_iff p).2 hp

/-- Completion sends every original trivial cofibration to an original trivial cofibration. -/
theorem completion_trivialCofibration {O : Type u} {C D : FixedDaggerCategory O}
    (F : C ⟶ D) (hF : trivialCofibrations (FixedDaggerCategory O) F) :
    trivialCofibrations (FixedStrictDaggerGroupoids O) ((fixedDaggerCompletion O).map F) := by
  letI : (fixedDaggerCompletionInclusionAdjunction O).IsQuillenAdjunction :=
    completionInclusion_isQuillen O
  letI : (fixedDaggerCompletion O).PreservesTrivialCofibrations :=
    Adjunction.IsQuillenAdjunction.preservesTrivialCofibrations
      (fixedDaggerCompletionInclusionAdjunction O)
  exact Functor.PreservesTrivialCofibrations.trivialCofibrations_le
    (fixedDaggerCompletion O) F hF

end
end DaggerOriginalFixedObjectDaggerCompletionQuillen
