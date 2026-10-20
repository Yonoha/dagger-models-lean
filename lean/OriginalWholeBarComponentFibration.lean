import NativeCoproductEvaluationFibration
import NativeCoproductDescFibration
import NativeReedyRelativeComponentFibration
import OriginalPiZeroBarProjectionFibration
import OriginalWholeBarRelativeReedy

/-! The exact whole-bar component projection and its actual relative replacement are fibrations. -/
set_option autoImplicit false
open CategoryTheory Limits HomotopicalAlgebra DaggerModels
open DaggerNativeCoproductEvaluationFibration DaggerNativeCoproductDescFibration
open DaggerNativeReedyRelativeComponentFibration DaggerNativeRowwiseWeakEvaluation
open DaggerOriginalWholeBarBisimplicial DaggerOriginalWholeBarRelativeReedy
open DaggerOriginalBarRowsPiZero DaggerOriginalNerveRowsPiZero
open DaggerOriginalSimplicialCategoryBarRows DaggerOriginalPiZeroBarProjectionFibration
open DaggerOriginalAmbientDaggerPiZeroGroupoid
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerOriginalWholeBarComponentFibration
noncomputable section

def componentArrowIso (C : SimplicialCat.{u, u}) :
    Arrow.mk (Limits.Sigma.desc (componentRowProjection C)) ≅
      Arrow.mk (componentMap (wholeProjection C)) :=
  Arrow.isoMk (whiskerSigmaIso SSet.π₀Functor (barRows C)) (Iso.refl _) (by
    change sigmaComparison (postcompose SSet.π₀Functor) (barRows C) ≫
      componentMap (wholeProjection C) = Limits.Sigma.desc (componentRowProjection C) ≫ 𝟙 _
    rw [Category.comp_id]
    apply Limits.Sigma.hom_ext
    intro z
    rw [← Category.assoc, ι_comp_sigmaComparison, Limits.Sigma.ι_desc]
    change (postcompose SSet.π₀Functor).map (Limits.Sigma.ι (barRows C) z) ≫
      (postcompose SSet.π₀Functor).map (wholeProjection C) = componentRowProjection C z
    rw [← Functor.map_comp]
    unfold wholeProjection
    rw [Limits.Sigma.ι_desc]
    rfl)

theorem whole_component_projection_fibration (C : SimplicialCat.{u, u})
    (hC : HasActualComponentGroupoid C) :
    Fibration (C := SSet.{u}) (componentMap (wholeProjection C)) := by
  have : ∀ z, Fibration (componentRowProjection C z) :=
    fun z ↦ component_projection_fibration C hC z
  have hp : Fibration (Limits.Sigma.desc (componentRowProjection C)) :=
    sigma_desc_fibration _
  exact (fibration_iff _).mpr
    (((fibrations SSet.{u}).arrow_mk_iso_iff (componentArrowIso C)).mp
      ((fibration_iff _).mp hp))

theorem replaced_whole_component_projection_fibration (C : SimplicialCat.{u, u})
    (hC : HasActualComponentGroupoid C) :
    Fibration (C := SSet.{u}) (componentMap (replacedBar C).hom) :=
  (component_fibration_iff (barArrow C)).mp (whole_component_projection_fibration C hC)

end
end DaggerOriginalWholeBarComponentFibration
