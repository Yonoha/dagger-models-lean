import ActualOrdinaryRigidificationFixedCofibrancy

/-! Apply the original localization criterion to the unchanged actual rigidification. -/
set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra DaggerModels
open DaggerModels.OrdinaryRigidification
open DaggerActualOrdinaryRigidificationFixedCofibrancy
open DaggerOriginalCofibrantDiagonalLocalizationWeak
open DaggerOriginalCofibrantLocalizationCriterion
open DaggerOriginalSimplicialCategoryDiagonalNerve
open DaggerOriginalSimplicialGroupoidCompletion
open DaggerOriginalAmbientDaggerPiZeroGroupoid
open scoped SSet.modelCategoryQuillen DaggerOriginalAmbientDaggerForgetCofibrancy
universe u
namespace DaggerActualOrdinaryRigidificationLocalization
noncomputable section

theorem diagonalLocalization_weak (X : SSet.{u}) :
    WeakEquivalence (diagonalLocalization (rigidification.obj X)) := by
  letI := fixed_isCofibrant X
  exact DaggerOriginalCofibrantDiagonalLocalizationWeak.diagonalLocalization_weak (fixed X)

theorem localizationHom_weak_iff_componentGroupoid (X : SSet.{u}) :
    (∀ x y : (rigidification.obj X).Obj,
      WeakEquivalence (localizationHom (rigidification.obj X) x y)) ↔
        HasActualComponentGroupoid (rigidification.obj X) := by
  letI := fixed_isCofibrant X
  exact
    DaggerOriginalCofibrantLocalizationCriterion.localizationHom_weak_iff_componentGroupoid
      (fixed X)

theorem localizationHom_weak (X : SSet.{u})
    (hX : HasActualComponentGroupoid (rigidification.obj X))
    (x y : (rigidification.obj X).Obj) :
    WeakEquivalence (localizationHom (rigidification.obj X) x y) :=
  (localizationHom_weak_iff_componentGroupoid X).mpr hX x y

end
end DaggerActualOrdinaryRigidificationLocalization
