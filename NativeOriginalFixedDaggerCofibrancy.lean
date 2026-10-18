import NativeOriginalFixedDaggerReplacement

/-! Exact native cofibrancy transport, dual to the previously proved fibrancy transport.
The legacy object-function equality is eliminated by the SAME original equivalence.
-/
set_option autoImplicit false
open CategoryTheory Limits HomotopicalAlgebra DaggerModels
open DaggerOriginalFixedObjectDaggerCategories DaggerOriginalFixedObjectLegacyDaggerEquivalence
open DaggerNativeOriginalFixedDaggerReplacement
open scoped SSet.modelCategoryQuillen DaggerOriginalFixedObjectAmbientDaggerModel
attribute [local instance] DaggerFixedCategoryModel.modelCategory
universe u
namespace DaggerNativeOriginalFixedDaggerCofibrancy
noncomputable section

theorem fromLegacy_cofibration {O : Type u} {C D : FixedDaggerSimplicialCat O} (F : C ⟶ D)
    [Cofibration F] : Cofibration (fromLegacyHom F) := by
  rw [cofibration_iff]
  change cofibrations (FixedDaggerSimplicialCat O) (toLegacyHom (fromLegacyHom F))
  rw [roundtrip_hom]
  exact (cofibration_iff F).mp inferInstance

theorem fromLegacy_cofibrant {O : Type u} (C : FixedDaggerSimplicialCat O) [IsCofibrant C] :
    IsCofibrant (fromLegacyObject C) := by
  letI : (fromLegacyFunctor O).IsLeftAdjoint :=
    (legacyDaggerEquivalence O).symm.toAdjunction.isLeftAdjoint
  have : Cofibration (initial.to C) := (isCofibrant_iff C).mp inferInstance
  have : Cofibration ((fromLegacyFunctor O).map (initial.to C)) :=
    fromLegacy_cofibration (initial.to C)
  exact (isCofibrant_iff_of_isInitial ((fromLegacyFunctor O).map (initial.to C))
    (IsInitial.isInitialObj (fromLegacyFunctor O) _ initialIsInitial)).mpr inferInstance

end
end DaggerNativeOriginalFixedDaggerCofibrancy
