import NativeOriginalFixedDaggerReplacement

/-! The EXACT ORIGINAL R preserves ALL native fixed-object weak maps,
by its unchanged natural unit and native two-out-of-three. No target invariance is assumed.
-/
set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra DaggerModels DaggerUnitaryInvariance
open DaggerOriginalFixedObjectDaggerCategories DaggerNativeOriginalFixedDaggerReplacement
open scoped SSet.modelCategoryQuillen DaggerOriginalFixedObjectAmbientDaggerModel
universe u
namespace DaggerNativeOriginalFixedRWeakPreservation
noncomputable section

theorem map_weak (R : FunctorialFibrantReplacement.{u})
    {C D : FixedDaggerCategory DaggerUnitaryInterval.Vertex.{u}} (F : C ⟶ D)
    [WeakEquivalence F] : WeakEquivalence ((replacement R).map F) := by
  have := unit_weak R C
  have := unit_weak R D
  have hf : WeakEquivalence (F ≫ unit R D) := inferInstance
  have : WeakEquivalence (unit R C ≫ (replacement R).map F) :=
    (unit_natural R F) ▸ hf
  exact weakEquivalence_of_precomp (unit R C) ((replacement R).map F)

end
end DaggerNativeOriginalFixedRWeakPreservation
