import OriginalCotensorOverEvaluationFibration
import OriginalCotensorEvaluationRowMaps

/-! Actual connected mapping-row evaluation is a Kan fibration for both original row diagrams. -/
set_option autoImplicit false
open CategoryTheory Simplicial Opposite MonoidalCategory MonoidalClosed HomotopicalAlgebra
open DaggerModels DaggerOriginalSimplicialCategoryBarRows
open DaggerOriginalConnectedMappingRowPiZero DaggerOriginalCotensorEvaluationRowMaps
open DaggerOriginalNerveRowsPiZero DaggerOriginalBarRowsPiZero
open DaggerOriginalCotensorPrecompositionWeak DaggerOriginalCotensorEvaluationNerveFibration
open DaggerOriginalCotensorOverEvaluationFibration DaggerOriginalAmbientDaggerPiZeroGroupoid
open DaggerOriginalConnectedCotensorRowIso DaggerOriginalConnectedCotensorBaseRows
open DaggerOriginalConnectedCotensorBarRows OriginalOrdinaryLocalKanReplacement
open DaggerOriginalPiZeroGroupoidLocalWeakInvariance
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerOriginalConnectedMappingEvaluationFibration
noncomputable section

def mappingBaseEvaluation {K : SSet.{u}} (a : 𝟙_ SSet.{u} ⟶ K) (C : SimplicialCat.{u, u}) :
    mappingBaseComponents K C ⟶ componentRows C :=
  Functor.whiskerRight (baseRowsEvaluation a C) SSet.π₀Functor

def mappingBarEvaluation {K : SSet.{u}} (a : 𝟙_ SSet.{u} ⟶ K) (C : SimplicialCat.{u, u})
    (z : C.Obj) : mappingBarComponents K C z ⟶ barComponentRows C z :=
  Functor.whiskerRight (barRowsEvaluation a C z) SSet.π₀Functor

theorem base_evaluation_square {K : SSet.{u}} [Subsingleton K.π₀]
    (a : 𝟙_ SSet.{u} ⟶ K) (v : K _⦋0⦌) (C : SimplicialCat.{u, u}) :
    (baseComponentsIhomIso K v C).hom ≫ mappingBaseEvaluation a C =
      componentRowsMap (evaluationFunctor a C) := by
  apply NatTrans.ext
  funext n q
  change SSet.mapπ₀ (DaggerOriginalFixedObjectCotensorPoints.pointEvaluation a _)
      (SSet.mapπ₀ (baseRowIhomIso K v C n.unop.len).hom q) =
    SSet.mapπ₀ ((DaggerOriginalNerveRowChainData.baseRowsMap (evaluationFunctor a C)).app n) q
  rw [← SSet.mapπ₀_comp_apply, ← baseRowIhomMap_eq_iso, base_row_evaluation_eq]
  simp only [SimplexCategory.mk_len, op_unop]

theorem bar_evaluation_square {K : SSet.{u}} [Subsingleton K.π₀]
    (a : 𝟙_ SSet.{u} ⟶ K) (v : K _⦋0⦌) (C : SimplicialCat.{u, u}) (z : C.Obj) :
    (barComponentsIhomIso K v C z).hom ≫ mappingBarEvaluation a C z =
      barComponentRowsMap (evaluationFunctor a C) z := by
  apply NatTrans.ext
  funext n q
  change SSet.mapπ₀ (DaggerOriginalFixedObjectCotensorPoints.pointEvaluation a _)
      (SSet.mapπ₀ (barRowIhomIso K v C z n.unop.len).hom q) =
    SSet.mapπ₀ ((barRowsMap (evaluationFunctor a C) z).app n) q
  rw [← SSet.mapπ₀_comp_apply, ← barRowIhomMap_eq_iso, bar_row_evaluation_eq]
  simp only [SimplexCategory.mk_len, op_unop]

theorem base_evaluation_fibration {K : SSet.{u}} [Subsingleton K.π₀]
    (a : 𝟙_ SSet.{u} ⟶ K) (v : K _⦋0⦌) (C : SimplicialCat.{u, u})
    (hC : HasActualComponentGroupoid C)
    (hH : ∀ x y : C.Obj, (C.enriched.Hom x y).KanComplex) :
    Fibration (mappingBaseEvaluation a C) := by
  have hp := evaluation_nerve_fibration a C hC hH
  let e := (baseComponentsIhomIso K v C).symm ≪≫ componentRowsIso (originalCotensor K C)
  let d : Arrow.mk (mappingBaseEvaluation a C) ≅
      Arrow.mk (nerveMap (DaggerOriginalSimplicialPiZeroCategory.componentFunctor
        (evaluationFunctor a C))) := Arrow.isoMk e (componentRowsIso C) (by
    dsimp [e]
    rw [Category.assoc, ← componentRowsIso_natural, ← base_evaluation_square a v C,
      ← Category.assoc, Iso.inv_hom_id_assoc])
  exact (HomotopicalAlgebra.fibration_iff _).mpr
    (((fibrations SSet.{u}).arrow_mk_iso_iff d).mpr
      ((HomotopicalAlgebra.fibration_iff _).mp hp))

theorem bar_evaluation_fibration {K : SSet.{u}} [Subsingleton K.π₀]
    (a : 𝟙_ SSet.{u} ⟶ K) (v : K _⦋0⦌) (C : SimplicialCat.{u, u})
    (hC : HasActualComponentGroupoid C)
    (hH : ∀ x y : C.Obj, (C.enriched.Hom x y).KanComplex) (z : C.Obj) :
    Fibration (mappingBarEvaluation a C z) := by
  have hp := evaluation_over_nerve_fibration a C hC hH z
  let e := (barComponentsIhomIso K v C z).symm ≪≫
    barComponentRowsIso (originalCotensor K C) z
  let d : Arrow.mk (mappingBarEvaluation a C z) ≅
      Arrow.mk (nerveMap (Over.post
        (DaggerOriginalSimplicialPiZeroCategory.componentFunctor (evaluationFunctor a C)) :
          Over (T := DaggerOriginalSimplicialPiZeroCategory.componentObjects
            (originalCotensor K C)) z ⥤
              Over (T := DaggerOriginalSimplicialPiZeroCategory.componentObjects C) z)) :=
    Arrow.isoMk e (barComponentRowsIso C z) (by
      dsimp [e]
      rw [Category.assoc, ← barComponentsIso_natural, ← bar_evaluation_square a v C z,
        ← Category.assoc, Iso.inv_hom_id_assoc]
      rfl)
  exact (HomotopicalAlgebra.fibration_iff _).mpr
    (((fibrations SSet.{u}).arrow_mk_iso_iff d).mpr
      ((HomotopicalAlgebra.fibration_iff _).mp hp))

theorem replacement_evaluation_fibrations {K : SSet.{u}} [Subsingleton K.π₀]
    (a : 𝟙_ SSet.{u} ⟶ K) (C : SimplicialCat.{u, u})
    (hC : HasActualComponentGroupoid C) :
    Fibration (mappingBaseEvaluation a (replacement.obj C)) ∧
      ∀ z : (replacement.obj C).Obj,
        Fibration (mappingBarEvaluation a (replacement.obj C) z) := by
  have h := (replacement_groupoid_iff C).mp hC
  have hh := replacement_locallyKan C
  let v := SSet.unitHomEquiv K a
  exact ⟨base_evaluation_fibration a v _ h hh, fun z ↦
    bar_evaluation_fibration a v _ h hh z⟩

theorem evaluation_projection_square {K : SSet.{u}}
    (a : 𝟙_ SSet.{u} ⟶ K) (C : SimplicialCat.{u, u}) (z : C.Obj) :
    mappingComponentProjection K C z ≫ mappingBaseEvaluation a C =
      mappingBarEvaluation a C z ≫ componentRowProjection C z := by
  apply NatTrans.ext
  funext n q
  obtain ⟨f, rfl⟩ := SSet.π₀.mk_surjective q
  rfl

end
end DaggerOriginalConnectedMappingEvaluationFibration
