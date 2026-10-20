import NativeFreePathUnitNerveWeak
import OriginalCofibrantFreeUnitReduction

/-! Actual original cofibrancy implies diagonal localization weakness without a free-unit input. -/
set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra DaggerModels
open DaggerOriginalFixedObjectSimplicialCategories DaggerOriginalSimplicialDegreeCategory
open DaggerOriginalDegreewiseCompletionCriterion DaggerOriginalSimplicialCategoryDiagonalNerve
open DaggerOriginalSimplicialGroupoidCompletion DaggerOriginalAmbientDaggerPiZeroGroupoid
open scoped SSet.modelCategoryQuillen DaggerOriginalAmbientDaggerForgetCofibrancy
universe u
namespace DaggerOriginalCofibrantDiagonalLocalizationWeak
noncomputable section

theorem degreeRetractData_of_cofibrant {O : Type u} (C : FixedSimplicialCategory O)
    [IsCofibrant C] : DegreeRetractData (original O C) :=
  DaggerOriginalCofibrantFreeUnitReduction.degreeRetractData_of_free_units C
    (fun n ↦ DaggerNativeFreePathUnitNerveWeak.unit_nerve_weak (degreeObjects (original O C) n))

theorem diagonalLocalization_weak {O : Type u} (C : FixedSimplicialCategory O)
    [IsCofibrant C] : WeakEquivalence (diagonalLocalization (original O C)) :=
  DaggerOriginalCofibrantFreeUnitReduction.diagonalLocalization_weak_of_free_units C
    (fun n ↦ DaggerNativeFreePathUnitNerveWeak.unit_nerve_weak (degreeObjects (original O C) n))

theorem localizationHom_weak {O : Type u} (C : FixedSimplicialCategory O)
    [IsCofibrant C] (hC : HasActualComponentGroupoid (original O C)) (x y : O) :
    WeakEquivalence (localizationHom (original O C) x y) :=
  DaggerOriginalCofibrantFreeUnitReduction.localizationHom_weak_of_free_units C hC
    (fun n ↦ DaggerNativeFreePathUnitNerveWeak.unit_nerve_weak (degreeObjects (original O C) n)) x y

end
end DaggerOriginalCofibrantDiagonalLocalizationWeak
