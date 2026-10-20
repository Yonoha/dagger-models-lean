import OriginalFixedObjectLegacyDaggerEquivalence
import OriginalFixedObjectGroupoidCompletionAdjunction
import Mathlib.CategoryTheory.Adjunction.Reflective

/-!
# Native colimits in the original fixed-object dagger categories

Transfer the legacy ambient colimits through the equivalence preserving every original Hom.
Then use the actual completion-inclusion adjunction to obtain strict dagger groupoid colimits.
No model structure on strict groupoids is assumed.
-/

set_option autoImplicit false
open CategoryTheory Limits DaggerModels
open DaggerOriginalFixedObjectDaggerCategories
open DaggerOriginalFixedObjectLegacyDaggerEquivalence
open DaggerOriginalFixedObjectGroupoidCompletionAdjunction
universe u
namespace DaggerOriginalFixedObjectDaggerColimits
noncomputable section

/-- Ambient colimits come from the unchanged legacy fixed dagger presentation. -/
instance fixedDaggerHasColimits (O : Type u) :
    HasColimitsOfSize.{u, u} (FixedDaggerCategory O) := by
  letI := DaggerFixedCategoryColimits.hasSmallColimits (O := O)
  exact Adjunction.has_colimits_of_equivalence (legacyDaggerEquivalence O).functor

/-- The original strict inclusion is full because it is the native full-subcategory inclusion. -/
instance fixedDaggerInclusion_full (O : Type u) : (fixedDaggerInclusion O).Full := by
  change (ObjectProperty.ι (IsStrictFixedDagger (O := O))).Full
  infer_instance

/-- The original strict inclusion is faithful on all original fixed dagger arrows. -/
instance fixedDaggerInclusion_faithful (O : Type u) : (fixedDaggerInclusion O).Faithful := by
  change (ObjectProperty.ι (IsStrictFixedDagger (O := O))).Faithful
  infer_instance

/-- Strict dagger completion exhibits the original strict subcategory as reflective. -/
instance fixedDaggerInclusion_reflective (O : Type u) : Reflective (fixedDaggerInclusion O) :=
  ⟨fixedDaggerCompletion O, fixedDaggerCompletionInclusionAdjunction O⟩

/-- Complete the ambient colimit to obtain the actual strict dagger groupoid colimit. -/
instance strictDaggerHasColimits (O : Type u) :
    HasColimitsOfSize.{u, u} (FixedStrictDaggerGroupoids O) :=
  CategoryTheory.hasColimits_of_reflective (fixedDaggerInclusion O)

/-- In particular, the original strict dagger groupoids have native finite colimits. -/
instance strictDaggerHasFiniteColimits (O : Type u) :
    HasFiniteColimits (FixedStrictDaggerGroupoids O) :=
  hasFiniteColimits_of_hasColimitsOfSize.{u, u} _

end
end DaggerOriginalFixedObjectDaggerColimits
