import OriginalFixedObjectDaggerColimits
import OriginalEquivalenceModelTransport
import OriginalEquivalenceQuillenTransport

/-!
# The native model on the exact original ambient fixed-object dagger category

Reuse the proved legacy fixed-object model through the full equivalence retaining the
original enrichment, dagger and all Hom maps. The ambient category is not identified
with its strict groupoid subcategory. Native limits and colimits are transferred from
the actual legacy presentation; no ambient model or factorization is assumed.
-/
set_option autoImplicit false
open CategoryTheory Limits HomotopicalAlgebra DaggerModels
open DaggerOriginalFixedObjectDaggerCategories DaggerOriginalFixedObjectLegacyDaggerEquivalence
open scoped SSet.modelCategoryQuillen
attribute [local instance] DaggerFixedCategoryModel.modelCategory
universe u
namespace DaggerOriginalFixedObjectAmbientDaggerModel
noncomputable section

/-- The actual original ambient category inherits all small limits through the full equivalence. -/
instance ambientHasLimits (O : Type u) : HasLimitsOfSize.{u, u} (FixedDaggerCategory O) := by
  letI := DaggerFixedCategoryMonadicLimits.hasSmallLimits (O := O)
  exact Adjunction.has_limits_of_equivalence (legacyDaggerEquivalence O).functor

/-- Actual ambient finite limits follow from the transferred original small limits. -/
instance ambientHasFiniteLimits (O : Type u) : HasFiniteLimits (FixedDaggerCategory O) :=
  hasFiniteLimits_of_hasLimitsOfSize.{u, u} _

/-- Actual ambient finite colimits follow from the already proved original small colimits. -/
instance ambientHasFiniteColimits (O : Type u) : HasFiniteColimits (FixedDaggerCategory O) :=
  hasFiniteColimits_of_hasColimitsOfSize.{u, u} _

/-- Retain exactly the existing model weak class on the full original enriched functor. -/
def ambientWeakEquivalences (O : Type u) : MorphismProperty (FixedDaggerCategory O) :=
  (weakEquivalences (FixedDaggerSimplicialCat O)).inverseImage (legacyDaggerEquivalence O).functor

/-- Retain exactly the existing model fibration class on the full original enriched functor. -/
def ambientFibrations (O : Type u) : MorphismProperty (FixedDaggerCategory O) :=
  (fibrations (FixedDaggerSimplicialCat O)).inverseImage (legacyDaggerEquivalence O).functor

/-- Retain exactly the existing model cofibration class on the full original enriched functor. -/
def ambientCofibrations (O : Type u) : MorphismProperty (FixedDaggerCategory O) :=
  (cofibrations (FixedDaggerSimplicialCat O)).inverseImage (legacyDaggerEquivalence O).functor

scoped instance ambientWeakStructure (O : Type u) :
    CategoryWithWeakEquivalences (FixedDaggerCategory O) := ⟨ambientWeakEquivalences O⟩

scoped instance ambientFibStructure (O : Type u) :
    CategoryWithFibrations (FixedDaggerCategory O) := ⟨ambientFibrations O⟩

scoped instance ambientCofStructure (O : Type u) :
    CategoryWithCofibrations (FixedDaggerCategory O) := ⟨ambientCofibrations O⟩

open scoped DaggerOriginalFixedObjectAmbientDaggerModel

/-- Unconditional native model on the exact original ambient fixed-object dagger category. -/
scoped instance ambientModel (O : Type u) : ModelCategory (FixedDaggerCategory O) :=
  DaggerOriginalEquivalenceModelTransport.transportModel (legacyDaggerEquivalence O) rfl rfl rfl

/-- The exact original ambient weak class is precisely the native class on every original Hom. -/
theorem weakEquivalence_iff_original {O : Type u} {C D : FixedDaggerCategory O} (F : C ⟶ D) :
    WeakEquivalence F ↔ ∀ x y : O, WeakEquivalence (F.underlying.map x y) := by
  rw [weakEquivalence_iff]
  change (∀ x y : O, WeakEquivalence (F.underlying.map x y)) ↔ _
  rfl

/-- The exact original ambient fibration class is precisely the native class on every
original Hom. -/
theorem fibration_iff_original {O : Type u} {C D : FixedDaggerCategory O} (F : C ⟶ D) :
    Fibration F ↔ ∀ x y : O, Fibration (F.underlying.map x y) := by
  rw [fibration_iff]
  change fibrations (FixedDaggerSimplicialCat O) ((legacyDaggerEquivalence O).functor.map F) ↔ _
  rw [← fibration_iff, DaggerFixedCategoryModel.fibration_iff_homwise]
  rfl

/-- Reusing the legacy presentation is a native Quillen equivalence for the exact same classes. -/
theorem legacyComparison_isQuillenEquivalence (O : Type u) :
    (legacyDaggerEquivalence O).symm.toAdjunction.IsQuillenEquivalence :=
  DaggerOriginalEquivalenceQuillenTransport.isQuillenEquivalence
    (legacyDaggerEquivalence O).symm rfl rfl rfl

end
end DaggerOriginalFixedObjectAmbientDaggerModel
