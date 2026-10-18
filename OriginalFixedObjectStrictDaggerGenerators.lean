import OriginalFixedObjectColimitModelRecognition
import OriginalAdjunctionMappedLifting
import FixedCategoryGenerators

/-!
# Exact reflected generators on the original fixed-object strict dagger groupoids

Map the existing boundary and horn generators by the actual groupoid completion.
Their right lifting classes are the unchanged original Homwise trivial fibrations and
fibrations. These equalities do not yet assert small object argument domain smallness.
-/

set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra DaggerModels
open DaggerOriginalFixedObjectSimplicialCategories DaggerOriginalFixedObjectDaggerCategories
open DaggerOriginalFixedObjectLegacyDaggerEquivalence
open DaggerOriginalFixedObjectGroupoidCompletionAdjunction
open DaggerOriginalFixedObjectGroupoidClasses
open scoped DaggerOriginalFixedObjectGroupoidClasses SSet.modelCategoryQuillen
universe u
namespace DaggerOriginalFixedObjectStrictDaggerGenerators
noncomputable section

/-- Complete the exact legacy fixed-object dagger enrichment into the original strict category. -/
def legacyStrictCompletion (O : Type u) :
    FixedDaggerSimplicialCat O ⥤ FixedStrictDaggerGroupoids O :=
  (legacyDaggerEquivalence O).inverse ⋙ fixedDaggerCompletion O

/-- Include the original strict dagger groupoid without changing any original Hom. -/
def strictLegacyInclusion (O : Type u) :
    FixedStrictDaggerGroupoids O ⥤ FixedDaggerSimplicialCat O :=
  fixedDaggerInclusion O ⋙ (legacyDaggerEquivalence O).functor

/-- Compose the actual presentation equivalence and actual completion-inclusion adjunction. -/
def legacyStrictAdjunction (O : Type u) : legacyStrictCompletion O ⊣ strictLegacyInclusion O :=
  (legacyDaggerEquivalence O).symm.toAdjunction.comp (fixedDaggerCompletionInclusionAdjunction O)

/-- The boundary generators are the full actual completion images, including arrow isos. -/
def strictI (O : Type u) : MorphismProperty (FixedStrictDaggerGroupoids O) :=
  (DaggerFixedCategoryGenerators.I O).map (legacyStrictCompletion O)

/-- The horn generators are the full actual completion images, including arrow isos. -/
def strictJ (O : Type u) : MorphismProperty (FixedStrictDaggerGroupoids O) :=
  (DaggerFixedCategoryGenerators.J O).map (legacyStrictCompletion O)

/-- Inclusion retains exactly every original Hom map, including the fixed object function. -/
theorem inclusion_map_hom {O : Type u} {C D : FixedStrictDaggerGroupoids O} (F : C ⟶ D)
    (x y : O) : ((strictLegacyInclusion O).map F).val.map x y = F.hom.underlying.map x y := rfl

/-- Boundary right lifting is precisely the specified original Homwise trivial-fibration class. -/
theorem strictI_rlp_eq (O : Type u) :
    (strictI O).rlp = strictDaggerFibrations O ⊓ strictDaggerWeakEquivalences O := by
  rw [strictI, DaggerOriginalAdjunctionMappedLifting.mapped_rlp_eq (legacyStrictAdjunction O),
    DaggerFixedCategoryGenerators.I_rlp_eq]
  funext C D F
  apply propext
  change ((∀ x y : O, Fibration (F.hom.underlying.map x y)) ∧
    (∀ x y : O, WeakEquivalence (F.hom.underlying.map x y))) ↔ _
  rw [← strictDagger_fibration_iff F, ← strictDagger_weakEquivalence_iff F]
  rw [fibration_iff F, weakEquivalence_iff F]
  rfl

/-- Horn right lifting is precisely the specified original Homwise fibration class. -/
theorem strictJ_rlp_eq (O : Type u) : (strictJ O).rlp = strictDaggerFibrations O := by
  rw [strictJ, DaggerOriginalAdjunctionMappedLifting.mapped_rlp_eq (legacyStrictAdjunction O),
    DaggerFixedCategoryGenerators.J_rlp_eq]
  funext C D F
  apply propext
  change (∀ x y : O, Fibration (F.hom.underlying.map x y)) ↔ _
  rw [← strictDagger_fibration_iff F]
  rw [fibration_iff F]
  rfl

/-- The exact generated left class is the already specified canonical cofibration class. -/
theorem strictI_rlp_llp_eq (O : Type u) :
    (strictI O).rlp.llp = DaggerOriginalFixedObjectCofibrations.strictDaggerCofibrations O := by
  rw [strictI_rlp_eq]
  rfl

end
end DaggerOriginalFixedObjectStrictDaggerGenerators
