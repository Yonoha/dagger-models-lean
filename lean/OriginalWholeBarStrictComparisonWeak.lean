import OriginalLocallyKanWholeBarStrictComparisonWeak
import OriginalWholeBarReedyDiagonalFibration
import OriginalBarLocalWeakComparisonInvariance
import OriginalWholeBarRowProperties
import NativeReedyReplacementWeakMaps
import NativeBisimplicialDiagonalWeak
import OriginalLocalKanReplacementDiagonalWeak

/-! The SAME original whole Hom-sum comparison is weak under the original component groupoid. -/
set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra DaggerModels
open DaggerOriginalWholeBarReedyStrictFibre DaggerOriginalWholeBarRelativeReedy
open DaggerOriginalLocallyKanWholeBarStrictComparisonWeak
open DaggerOriginalWholeBarReedyDiagonalFibration DaggerOriginalBarLocalWeakComparisonInvariance
open DaggerOriginalWholeBarRowProperties DaggerOriginalNerveLocalWeakPreservation
open DaggerOriginalNerveRowChainData DaggerOriginalSimplicialCategoryWholeBarFibreFunctor
open DaggerNativeReedyReplacementWeakMaps DaggerNativeBisimplicialDiagonalWeak
open DaggerNativeBisimplicialDiagonal DaggerNativeSSetFibrationSquareFibreWeak
open DaggerOriginalLocalKanReplacementDiagonalWeak
open DaggerOriginalAmbientDaggerPiZeroGroupoid DaggerOriginalPiZeroGroupoidLocalWeakInvariance
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerOriginalWholeBarStrictComparisonWeak
noncomputable section

theorem replaced_total_map_weak_of_local {C D : SimplicialCat.{u, u}} (F : C ⟶ D)
    (hO : Function.Bijective F.obj)
    (hF : ∀ x y : C.Obj, WeakEquivalence (F.map x y)) :
    WeakEquivalence (diagonalFunctor.map (replacedBarMap F).left) :=
  diagonal_map_weak _ (relative_total_map_row_weak (barArrowMap F)
    (wholeRowsMap_row_weak F hO hF))

theorem replaced_base_map_weak_of_local {C D : SimplicialCat.{u, u}} (F : C ⟶ D)
    (hO : Function.Bijective F.obj)
    (hF : ∀ x y : C.Obj, WeakEquivalence (F.map x y)) :
    WeakEquivalence (diagonalFunctor.map (replacedBarMap F).right) := by
  have hb : ∀ h, WeakEquivalence ((baseRowsMap F).app h) := by
    intro h
    obtain ⟨h⟩ := h
    induction h using SimplexCategory.rec with | _ n =>
      exact baseRowsMap_weak F hO hF n
  exact diagonal_map_weak _ (relative_base_map_row_weak (barArrowMap F) hb)

theorem fibreMap_weak_of_local {C D : SimplicialCat.{u, u}} (F : C ⟶ D)
    (hC : HasActualComponentGroupoid C) (hD : HasActualComponentGroupoid D)
    (hO : Function.Bijective F.obj)
    (hF : ∀ x y : C.Obj, WeakEquivalence (F.map x y)) (x : C.Obj) :
    WeakEquivalence (DaggerOriginalWholeBarReedyStrictFibre.fibreMap F x) := by
  have : Fibration (projection C) := projection_fibration C hC
  have : Fibration (projection D) := projection_fibration D hD
  have := replaced_total_map_weak_of_local F hO hF
  have := replaced_base_map_weak_of_local F hO hF
  unfold DaggerOriginalWholeBarReedyStrictFibre.fibreMap
  exact fibreMap_weakEquivalence _ _ _ _ _ _ _ _

theorem strictComparison_weak (C : SimplicialCat.{u, u})
    (hC : HasActualComponentGroupoid C) (x : C.Obj) :
    WeakEquivalence (strictComparison C x) := by
  let D := OriginalOrdinaryLocalKanReplacement.replacement.obj C
  let u : C ⟶ D := OriginalOrdinaryLocalKanReplacement.unit.app C
  have hD : HasActualComponentGroupoid D := (replacement_groupoid_iff C).mp hC
  have : ∀ y z : D.Obj, IsFibrant (D.enriched.Hom y z) :=
    OriginalOrdinaryLocalKanReplacement.replacement_locallyKan C
  have : WeakEquivalence (strictComparison D (u.obj x)) :=
    strictComparison_weak_of_locallyKan D (u.obj x)
  have : WeakEquivalence (originalHomSumMap u x) := originalHomSumMap_weak u
    (OriginalOrdinaryLocalKanReplacement.unit_obj_bijective C) (unit_hom_weak C) x
  have : WeakEquivalence (DaggerOriginalWholeBarReedyStrictFibre.fibreMap u x) :=
    fibreMap_weak_of_local u hC hD (OriginalOrdinaryLocalKanReplacement.unit_obj_bijective C)
      (unit_hom_weak C) x
  have : WeakEquivalence (originalHomSumMap u x ≫ strictComparison D (u.obj x)) := inferInstance
  exact weakEquivalence_of_postcomp_of_fac (strictComparison_natural u x)

end
end DaggerOriginalWholeBarStrictComparisonWeak
