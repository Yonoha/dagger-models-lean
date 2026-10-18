import OriginalWholeBarReedyFibreIdentifications
import OriginalWholeBarRowsProjectionFibration
import NativeRelativeReedyFibreComparisonWeak

/-! The SAME full original Hom-sum strict comparison is weak for every locally Kan category. -/
set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra DaggerModels
open DaggerOriginalWholeBarReedyFibreIdentifications DaggerOriginalWholeBarRowsProjectionFibration
open DaggerOriginalWholeBarBisimplicialPoint DaggerOriginalWholeBarRelativeReedy
open DaggerOriginalWholeBarReedyStrictFibre DaggerNativeRelativeReedyFibreComparisonWeak
open DaggerNativeRelativeReedyBisimplicialFibres DaggerNativeBisimplicialDiagonal
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerOriginalLocallyKanWholeBarStrictComparisonWeak
noncomputable section

theorem strictComparison_weak_of_locallyKan (C : SimplicialCat.{u, u})
    [∀ x y : C.Obj, IsFibrant (C.enriched.Hom x y)] (x : C.Obj) :
    WeakEquivalence (strictComparison C x) := by
  have : WeakEquivalence
      (imageComparison diagonalFunctor (barArrow C) (sourcePoint C x)) :=
    diagonalComparison_weak (barArrow C) (whole_row_projection_fibration C) (sourcePoint C x)
  rw [← strictComparison_factor]
  infer_instance

end
end DaggerOriginalLocallyKanWholeBarStrictComparisonWeak
