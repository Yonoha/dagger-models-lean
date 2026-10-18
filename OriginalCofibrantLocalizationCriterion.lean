import OriginalCofibrantDiagonalLocalizationWeak
import OriginalLocalizationHomWeakFromDiagonal

/-! The exact original cofibrant localization criterion has no remaining diagonal-weakness input. -/
set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra DaggerModels
open DaggerOriginalFixedObjectSimplicialCategories DaggerOriginalSimplicialCategoryDiagonalNerve
open DaggerOriginalSimplicialGroupoidCompletion DaggerOriginalAmbientDaggerPiZeroGroupoid
open DaggerOriginalCofibrantDiagonalLocalizationWeak DaggerOriginalFixedObjectDaggerCategories
open DaggerOriginalFixedObjectGroupoidTerminals DaggerOriginalAmbientDaggerForgetCofibrancy
open scoped SSet.modelCategoryQuillen DaggerOriginalAmbientDaggerForgetCofibrancy
  DaggerOriginalFixedObjectAmbientDaggerModel
universe u
namespace DaggerOriginalCofibrantLocalizationCriterion
noncomputable section

theorem localizationHom_weak_iff_componentGroupoid {O : Type u} (C : FixedSimplicialCategory O)
    [IsCofibrant C] :
    (∀ x y : O, WeakEquivalence (localizationHom (original O C) x y)) ↔
      HasActualComponentGroupoid (original O C) :=
  DaggerOriginalLocalizationHomWeakFromDiagonal.localizationHom_weak_iff_groupoid_given_diagonal
    _ (diagonalLocalization_weak C)

theorem interval_localizationHom_weak {O : Type u} {H : FixedDaggerCategory O}
    (f : H ⟶ terminalFixedDagger O) [IsCofibrant H] [WeakEquivalence f] (x y : O) :
    WeakEquivalence (localizationHom (original O H.underlying) x y) := by
  have : IsCofibrant H.underlying := forget_isCofibrant H
  exact localizationHom_weak H.underlying (interval_hasActualComponentGroupoid f) x y

end
end DaggerOriginalCofibrantLocalizationCriterion
