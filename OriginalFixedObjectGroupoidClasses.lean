import OriginalFixedObjectProductLimits
import Mathlib.AlgebraicTopology.ModelCategory.PathObject

/-!
# The exact Homwise classes on the original fixed-object strict groupoids

Use the inverse image of the native simplicial weak-equivalence and fibration
classes under every original Hom evaluation. These category structures specify
the intended classes; they do not assert the existence of a ModelCategory.
The native closure properties follow from the actual evaluation functors.
-/

set_option autoImplicit false
open CategoryTheory Limits HomotopicalAlgebra DaggerModels
open DaggerOriginalFixedObjectSimplicialCategories DaggerOriginalFixedObjectDaggerCategories
open scoped SSet.modelCategoryQuillen
universe u

namespace DaggerOriginalFixedObjectGroupoidClasses

noncomputable section

/-- The original Hom evaluation retains the exact native object and arrow. -/
def homEvaluation (O : Type u) (x y : O) : FixedSimplicialCategory O ⥤ SSet.{u} where
  obj C := C.enriched.Hom x y
  map F := F.map x y

/-- Evaluate the same original Hom on the strict full subcategory. -/
def strictHomEvaluation (O : Type u) (x y : O) : FixedStrictGroupoids O ⥤ SSet.{u} :=
  ObjectProperty.ι (IsStrictFixed (O := O)) ⋙ homEvaluation O x y

/-- Evaluate the same original Hom after forgetting only the dagger. -/
def strictDaggerHomEvaluation (O : Type u) (x y : O) :
    FixedStrictDaggerGroupoids O ⥤ SSet.{u} :=
  fixedStrictDaggerForget O ⋙ strictHomEvaluation O x y

/-- The intended weak class is precisely the native weak class on every original Hom. -/
def strictWeakEquivalences (O : Type u) : MorphismProperty (FixedStrictGroupoids O) :=
  ⨅ x : O, ⨅ y : O, (weakEquivalences SSet.{u}).inverseImage (strictHomEvaluation O x y)

/-- The intended fibration class is precisely the native fibration class on every original Hom. -/
def strictFibrations (O : Type u) : MorphismProperty (FixedStrictGroupoids O) :=
  ⨅ x : O, ⨅ y : O, (fibrations SSet.{u}).inverseImage (strictHomEvaluation O x y)

instance strictWeakTwoOutOfThree (O : Type u) :
    (strictWeakEquivalences O).HasTwoOutOfThreeProperty := by
  unfold strictWeakEquivalences
  infer_instance

instance strictWeakRetracts (O : Type u) :
    (strictWeakEquivalences O).IsStableUnderRetracts := by
  unfold strictWeakEquivalences
  infer_instance

instance strictFibMultiplicative (O : Type u) : (strictFibrations O).IsMultiplicative := by
  unfold strictFibrations
  infer_instance

/-- Native weak-equivalence data for the exact original Homwise class. -/
scoped instance strictWeakStructure (O : Type u) :
    CategoryWithWeakEquivalences (FixedStrictGroupoids O) where
  weakEquivalences := strictWeakEquivalences O

/-- Native fibration data for the exact original Homwise class. -/
scoped instance strictFibStructure (O : Type u) :
    CategoryWithFibrations (FixedStrictGroupoids O) where
  fibrations := strictFibrations O

/-- The dagger weak class uses exactly the same unchanged original Hom evaluations. -/
def strictDaggerWeakEquivalences (O : Type u) :
    MorphismProperty (FixedStrictDaggerGroupoids O) :=
  ⨅ x : O, ⨅ y : O, (weakEquivalences SSet.{u}).inverseImage (strictDaggerHomEvaluation O x y)

/-- The dagger fibration class uses exactly the same unchanged original Hom evaluations. -/
def strictDaggerFibrations (O : Type u) : MorphismProperty (FixedStrictDaggerGroupoids O) :=
  ⨅ x : O, ⨅ y : O, (fibrations SSet.{u}).inverseImage (strictDaggerHomEvaluation O x y)

instance strictDaggerWeakTwoOutOfThree (O : Type u) :
    (strictDaggerWeakEquivalences O).HasTwoOutOfThreeProperty := by
  unfold strictDaggerWeakEquivalences
  infer_instance

instance strictDaggerWeakRetracts (O : Type u) :
    (strictDaggerWeakEquivalences O).IsStableUnderRetracts := by
  unfold strictDaggerWeakEquivalences
  infer_instance

instance strictDaggerFibMultiplicative (O : Type u) :
    (strictDaggerFibrations O).IsMultiplicative := by
  unfold strictDaggerFibrations
  infer_instance

/-- Native weak-equivalence data retains the exact original dagger Homwise class. -/
scoped instance strictDaggerWeakStructure (O : Type u) :
    CategoryWithWeakEquivalences (FixedStrictDaggerGroupoids O) where
  weakEquivalences := strictDaggerWeakEquivalences O

/-- Native fibration data retains the exact original dagger Homwise class. -/
scoped instance strictDaggerFibStructure (O : Type u) :
    CategoryWithFibrations (FixedStrictDaggerGroupoids O) where
  fibrations := strictDaggerFibrations O

open scoped DaggerOriginalFixedObjectGroupoidClasses

/-- Weak equivalences in the specified original strict category are exactly Homwise weak maps. -/
theorem strict_weakEquivalence_iff {O : Type u} {C D : FixedStrictGroupoids O} (F : C ⟶ D) :
    WeakEquivalence F ↔ ∀ x y : O, WeakEquivalence (F.hom.map x y) := by
  rw [weakEquivalence_iff]
  change strictWeakEquivalences O F ↔ _
  simp only [strictWeakEquivalences, MorphismProperty.iInf_iff,
    MorphismProperty.inverseImage_iff]
  change (∀ x y : O, weakEquivalences SSet.{u} (F.hom.map x y)) ↔ _
  constructor
  · intro h x y
    exact (weakEquivalence_iff _).2 (h x y)
  · intro h x y
    exact (weakEquivalence_iff _).1 (h x y)

/-- Fibrations in the specified original strict category are exactly Homwise fibrations. -/
theorem strict_fibration_iff {O : Type u} {C D : FixedStrictGroupoids O} (F : C ⟶ D) :
    Fibration F ↔ ∀ x y : O, Fibration (F.hom.map x y) := by
  rw [fibration_iff]
  change strictFibrations O F ↔ _
  simp only [strictFibrations, MorphismProperty.iInf_iff, MorphismProperty.inverseImage_iff]
  change (∀ x y : O, fibrations SSet.{u} (F.hom.map x y)) ↔ _
  constructor
  · intro h x y
    exact (fibration_iff _).2 (h x y)
  · intro h x y
    exact (fibration_iff _).1 (h x y)

/-- Dagger weak equivalences are exactly native weak equivalences of all original Hom maps. -/
theorem strictDagger_weakEquivalence_iff {O : Type u}
    {C D : FixedStrictDaggerGroupoids O} (F : C ⟶ D) :
    WeakEquivalence F ↔ ∀ x y : O, WeakEquivalence (F.hom.underlying.map x y) := by
  rw [weakEquivalence_iff]
  change strictDaggerWeakEquivalences O F ↔ _
  simp only [strictDaggerWeakEquivalences, MorphismProperty.iInf_iff,
    MorphismProperty.inverseImage_iff]
  change (∀ x y : O, weakEquivalences SSet.{u} (F.hom.underlying.map x y)) ↔ _
  constructor
  · intro h x y
    exact (weakEquivalence_iff _).2 (h x y)
  · intro h x y
    exact (weakEquivalence_iff _).1 (h x y)

/-- Dagger fibrations are exactly native fibrations of all original Hom maps. -/
theorem strictDagger_fibration_iff {O : Type u}
    {C D : FixedStrictDaggerGroupoids O} (F : C ⟶ D) :
    Fibration F ↔ ∀ x y : O, Fibration (F.hom.underlying.map x y) := by
  rw [fibration_iff]
  change strictDaggerFibrations O F ↔ _
  simp only [strictDaggerFibrations, MorphismProperty.iInf_iff,
    MorphismProperty.inverseImage_iff]
  change (∀ x y : O, fibrations SSet.{u} (F.hom.underlying.map x y)) ↔ _
  constructor
  · intro h x y
    exact (fibration_iff _).2 (h x y)
  · intro h x y
    exact (fibration_iff _).1 (h x y)

end

end DaggerOriginalFixedObjectGroupoidClasses
