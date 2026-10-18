import NativeIhomWeakBetweenKan
import OriginalSimplicialPiZeroWeakEquivalence
import OriginalFixedObjectCotensorPoints
import TopCatModelCategory.ModelCategorySSet

/-! On Kan rows, realization units identify the actual component evaluation arrows. -/
set_option autoImplicit false
open CategoryTheory MonoidalCategory MonoidalClosed HomotopicalAlgebra
open DaggerNativeIhomWeakBetweenKan DaggerOriginalSimplicialPiZeroWeakEquivalence
open DaggerOriginalFixedObjectCotensorPoints
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeMappingEvaluationRealizationUnit
noncomputable section

def componentUnit (F : SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    F ⋙ SSet.π₀Functor ⟶ F ⋙ (SSet.toTop ⋙ TopCat.toSSet) ⋙ SSet.π₀Functor :=
  Functor.whiskerLeft F (Functor.whiskerRight sSetTopAdj.unit SSet.π₀Functor)

instance componentUnit_isIso (F : SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    IsIso (componentUnit F) := by
  have : ∀ n, IsIso ((componentUnit F).app n) := fun n ↦
    (isIso_iff_bijective _).mpr (SSet.bijective_mapπ₀_sSetTopAdj_unit_app (F.obj n))
  exact NatIso.isIso_of_isIso_app _

def mappingComponentUnit (F : SimplexCategoryᵒᵖ ⥤ SSet.{u}) (K : SSet.{u}) :
    F ⋙ ihom K ⋙ SSet.π₀Functor ⟶
      F ⋙ (SSet.toTop ⋙ TopCat.toSSet) ⋙ ihom K ⋙ SSet.π₀Functor :=
  Functor.whiskerLeft F
    (Functor.whiskerRight (Functor.whiskerRight sSetTopAdj.unit (ihom K)) SSet.π₀Functor)

instance mappingComponentUnit_isIso (F : SimplexCategoryᵒᵖ ⥤ SSet.{u}) (K : SSet.{u})
    [∀ n, IsFibrant (F.obj n)] : IsIso (mappingComponentUnit F K) := by
  have : ∀ n, IsIso ((mappingComponentUnit F K).app n) := by
    intro n
    have : WeakEquivalence ((ihom K).map (sSetTopAdj.unit.app (F.obj n))) :=
      ihom_map_weak K _
    exact (isIso_iff_bijective _).mpr
      (bijective_mapPiZero ((ihom K).map (sSetTopAdj.unit.app (F.obj n))))
  exact NatIso.isIso_of_isIso_app _

def rowEvaluation (F : SimplexCategoryᵒᵖ ⥤ SSet.{u}) {K : SSet.{u}}
    (a : 𝟙_ SSet.{u} ⟶ K) :
    (F ⋙ ihom K ⋙ SSet.π₀Functor : SSet.{u}) ⟶ (F ⋙ SSet.π₀Functor : SSet.{u}) where
  app n := SSet.mapπ₀ (pointEvaluation a (F.obj n))
  naturality n m f := by
    have h := congrArg SSet.π₀Functor.map (pointEvaluation_natural a (F.map f))
    simpa only [Functor.map_comp] using h

theorem evaluation_unit_square (F : SimplexCategoryᵒᵖ ⥤ SSet.{u}) {K : SSet.{u}}
    (a : 𝟙_ SSet.{u} ⟶ K) :
    mappingComponentUnit F K ≫ rowEvaluation (F ⋙ (SSet.toTop ⋙ TopCat.toSSet)) a =
      rowEvaluation F a ≫ componentUnit F := by
  apply NatTrans.ext
  funext n c
  change SSet.mapπ₀ (pointEvaluation a _)
    (SSet.mapπ₀ ((ihom K).map (sSetTopAdj.unit.app (F.obj n))) c) =
      SSet.mapπ₀ (sSetTopAdj.unit.app (F.obj n)) (SSet.mapπ₀ (pointEvaluation a _) c)
  rw [← SSet.mapπ₀_comp_apply, pointEvaluation_natural, SSet.mapπ₀_comp_apply]

def evaluationUnitArrowIso (F : SimplexCategoryᵒᵖ ⥤ SSet.{u})
    [∀ n, IsFibrant (F.obj n)] {K : SSet.{u}} (a : 𝟙_ SSet.{u} ⟶ K) :
    Arrow.mk (rowEvaluation F a) ≅
      Arrow.mk (rowEvaluation (F ⋙ (SSet.toTop ⋙ TopCat.toSSet)) a) :=
  Arrow.isoMk (asIso (mappingComponentUnit F K)) (asIso (componentUnit F))
    (evaluation_unit_square F a)

theorem realized_evaluation_fibration (F : SimplexCategoryᵒᵖ ⥤ SSet.{u})
    [∀ n, IsFibrant (F.obj n)] {K : SSet.{u}} (a : 𝟙_ SSet.{u} ⟶ K)
    [Fibration (C := SSet.{u}) (rowEvaluation F a)] :
    Fibration (C := SSet.{u})
      (rowEvaluation (F ⋙ (SSet.toTop ⋙ TopCat.toSSet)) a) := by
  exact (HomotopicalAlgebra.fibration_iff (C := SSet.{u}) _).mpr
    (((fibrations SSet.{u}).arrow_mk_iso_iff (evaluationUnitArrowIso F a)).mp
      ((HomotopicalAlgebra.fibration_iff (C := SSet.{u}) _).mp inferInstance))

end
end DaggerNativeMappingEvaluationRealizationUnit
