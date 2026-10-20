import NativeGroupoidOverEvaluationFibration
import OriginalCotensorEvaluationNerveFibration

/-! Original constants lift every actual over-category object through cotensor evaluation. -/
set_option autoImplicit false
open CategoryTheory Simplicial MonoidalCategory MonoidalClosed HomotopicalAlgebra DaggerModels
open DaggerOriginalSimplicialPiZeroCategory DaggerOriginalFixedObjectCotensorPoints
open DaggerOriginalCotensorPrecompositionWeak DaggerOriginalCotensorPiZeroGroupoid
open DaggerOriginalCotensorEvaluationNerveFibration DaggerOriginalAmbientDaggerPiZeroGroupoid
open DaggerNativeGroupoidOverEvaluationFibration DaggerOriginalOverNerveFibreChallengeProof
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerOriginalCotensorOverEvaluationFibration
noncomputable section

theorem evaluation_over_objects_surjective {K : SSet.{u}} (a : 𝟙_ SSet.{u} ⟶ K)
    (C : SimplicialCat.{u, u}) (z : C.Obj) : Function.Surjective
      (Over.post (componentFunctor (evaluationFunctor a C)) :
        Over (T := componentObjects (originalCotensor K C)) z ⥤
          Over (T := componentObjects C) z).obj := by
  intro B
  let f : ((originalCotensor K C).enriched.Hom B.left z).π₀ :=
    SSet.mapπ₀ (constantHom K (C.enriched.Hom B.left z)) B.hom
  let A := @Over.mk (componentObjects (originalCotensor K C))
    (componentCategory (originalCotensor K C)) z B.left f
  refine ⟨A, ?_⟩
  apply overObject_eq
    (a := (Over.post (componentFunctor (evaluationFunctor a C))).obj A)
    (b := B) rfl
  apply heq_of_eq
  change SSet.mapπ₀ (pointEvaluation a (C.enriched.Hom B.left z))
    (SSet.mapπ₀ (constantHom K (C.enriched.Hom B.left z)) B.hom) = B.hom
  rw [← SSet.mapπ₀_comp_apply, constantHom_evaluation, SSet.mapπ₀_id_apply]

theorem evaluation_over_nerve_fibration {K : SSet.{u}} (a : 𝟙_ SSet.{u} ⟶ K)
    (C : SimplicialCat.{u, u}) (hC : HasActualComponentGroupoid C)
    (hH : ∀ x y : C.Obj, (C.enriched.Hom x y).KanComplex) (z : C.Obj) :
    Fibration (nerveMap (Over.post (componentFunctor (evaluationFunctor a C)) :
      Over (T := componentObjects (originalCotensor K C)) z ⥤
        Over (T := componentObjects C) z)) :=
  over_nerve_fibration_of_groupoid_categories (cotensor_groupoid K C hC hH) hC
    (componentFunctor (evaluationFunctor a C)) z (evaluation_over_objects_surjective a C z)

end
end DaggerOriginalCotensorOverEvaluationFibration
