import OriginalFixedObjectMappingPathFactorization

/-!
# Native actual weak-equivalence/fibration factorization data

Package the proved entire original mapping-path factorization in Mathlib's
MapFactorizationData and HasFactorization for the exact original classes.
The left factor is proved weak; no claim of cofibrancy or lifting is made.
-/

set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra DaggerModels
open DaggerOriginalFixedObjectSimplicialCategories DaggerOriginalFixedObjectDaggerCategories
open DaggerOriginalFixedObjectGroupoidClasses DaggerOriginalFixedObjectMappingPathFactorization
open scoped SSet.modelCategoryQuillen DaggerOriginalFixedObjectGroupoidClasses
universe u
namespace DaggerOriginalFixedObjectMappingPathData
noncomputable section

/-- The actual original factorization in the exact two specified native classes. -/
def strictMappingPathData {O : Type u} {C D : FixedStrictGroupoids O} (F : C ⟶ D) :
    (strictWeakEquivalences O).MapFactorizationData (strictFibrations O) F where
  Z := mappingPath F
  i := mappingInclusion F
  p := mappingProjection F
  fac := mappingInclusion_projection F
  hi := (weakEquivalence_iff (mappingInclusion F)).1 (mappingInclusion_weakEquivalence F)
  hp := (fibration_iff (mappingProjection F)).1 (mappingProjection_fibration F)

/-- Every entire original arrow has that actual weak/fibration factorization. -/
instance strictWeakFibFactorization (O : Type u) :
    (strictWeakEquivalences O).HasFactorization (strictFibrations O) :=
  ⟨fun F ↦ ⟨strictMappingPathData F⟩⟩

/-- The exact dagger factorization keeps the full original enriched dagger functors. -/
def strictDaggerMappingPathData {O : Type u} {C D : FixedStrictDaggerGroupoids O}
    (F : C ⟶ D) :
    (strictDaggerWeakEquivalences O).MapFactorizationData (strictDaggerFibrations O) F where
  Z := daggerMappingPath F
  i := daggerMappingInclusion F
  p := daggerMappingProjection F
  fac := daggerMappingInclusion_projection F
  hi := (weakEquivalence_iff (daggerMappingInclusion F)).1
    (daggerMappingInclusion_weakEquivalence F)
  hp := (fibration_iff (daggerMappingProjection F)).1 (daggerMappingProjection_fibration F)

/-- Every entire original dagger arrow has the exact actual weak/fibration factorization. -/
instance strictDaggerWeakFibFactorization (O : Type u) :
    (strictDaggerWeakEquivalences O).HasFactorization (strictDaggerFibrations O) :=
  ⟨fun F ↦ ⟨strictDaggerMappingPathData F⟩⟩

end
end DaggerOriginalFixedObjectMappingPathData
