import NativeFullGroupoidNerveFibration
import OriginalCotensorPiZeroGroupoid
import OriginalFixedObjectCotensorPoints

/-! Original cotensor evaluation is full on actual components and has a Kan-fibration nerve. -/
set_option autoImplicit false
open CategoryTheory Simplicial Opposite MonoidalCategory MonoidalClosed HomotopicalAlgebra
open DaggerModels DaggerOriginalSimplicialPiZeroCategory
open DaggerOriginalFixedObjectCotensorPoints DaggerOriginalCotensorPrecompositionWeak
open DaggerOriginalCotensorPiZeroGroupoid DaggerOriginalAmbientDaggerPiZeroGroupoid
open DaggerNativeFullGroupoidNerveFibration
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerOriginalCotensorEvaluationNerveFibration
noncomputable section

def evaluationFunctor {K : SSet.{u}} (a : 𝟙_ SSet.{u} ⟶ K)
    (C : SimplicialCat.{u, u}) : originalCotensor K C ⟶ C where
  obj x := x
  map x y := pointEvaluation a (C.enriched.Hom x y)
  map_id x := (evaluation a ⟨C.enriched⟩).map_id x
  map_comp x y z := (evaluation a ⟨C.enriched⟩).map_comp x y z

theorem evaluation_components_surjective {K : SSet.{u}} (a : 𝟙_ SSet.{u} ⟶ K)
    (C : SimplicialCat.{u, u}) (x y : C.Obj) :
    Function.Surjective ((componentFunctor (evaluationFunctor a C)).map (X := x) (Y := y)) := by
  intro f
  refine ⟨SSet.mapπ₀ (constantHom K (C.enriched.Hom x y)) f, ?_⟩
  change SSet.mapπ₀ (pointEvaluation a (C.enriched.Hom x y))
    (SSet.mapπ₀ (constantHom K (C.enriched.Hom x y)) f) = f
  rw [← SSet.mapπ₀_comp_apply, constantHom_evaluation, SSet.mapπ₀_id_apply]

instance evaluation_component_full {K : SSet.{u}} (a : 𝟙_ SSet.{u} ⟶ K)
    (C : SimplicialCat.{u, u}) : (componentFunctor (evaluationFunctor a C)).Full :=
  ⟨fun {x y} ↦ evaluation_components_surjective a C x y⟩

theorem evaluation_nerve_fibration {K : SSet.{u}} (a : 𝟙_ SSet.{u} ⟶ K)
    (C : SimplicialCat.{u, u}) (hC : HasActualComponentGroupoid C)
    (hH : ∀ x y : C.Obj, (C.enriched.Hom x y).KanComplex) :
    Fibration (nerveMap (componentFunctor (evaluationFunctor a C))) :=
  full_nerve_fibration_of_groupoid_categories (cotensor_groupoid K C hC hH) hC
    (componentFunctor (evaluationFunctor a C)) (fun x ↦ ⟨x, rfl⟩)

end
end DaggerOriginalCotensorEvaluationNerveFibration
