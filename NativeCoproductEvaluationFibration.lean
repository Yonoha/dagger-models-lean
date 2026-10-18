import NativeBisimplicialHorizontalMapping
import NativeConnectedIhomCoproducts
import NativeCoproductMapFibration
import NativeMappingEvaluationRealizationUnit
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-! Connected-parameter evaluation on whole coproduct rows is the exact coproduct evaluation. -/
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory MonoidalClosed Simplicial HomotopicalAlgebra
open DaggerNativeBisimplicialHorizontalMapping DaggerNativeConnectedIhomCoproducts
open DaggerNativeMappingEvaluationRealizationUnit DaggerOriginalFixedObjectCotensorPoints
open DaggerNativeCoproductMapFibration
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeCoproductEvaluationFibration
noncomputable section

def postcompose (H : SSet.{u} ⥤ Type u) : BiSSet.{u} ⥤ SSet.{u} :=
  (Functor.whiskeringRight SimplexCategoryᵒᵖ SSet.{u} (Type u)).obj H

def whiskerSigmaIso {I : Type u} (H : SSet.{u} ⥤ Type u)
    [PreservesColimitsOfShape (Discrete I) H] (F : I → BiSSet.{u}) :
    (∐ fun i ↦ F i ⋙ H) ≅ (∐ F) ⋙ H := by
  have : PreservesColimitsOfShape (Discrete I) (postcompose H) := by
    exact CategoryTheory.whiskeringRight_preservesColimitsOfShape H
  exact asIso (sigmaComparison (postcompose H) F)

theorem evaluation_comparison_square {I : Type u} (F : I → BiSSet.{u})
    {K : SSet.{u}} (a : 𝟙_ SSet.{u} ⟶ K) :
    sigmaComparison (postcompose (ihom K ⋙ SSet.π₀Functor)) F ≫
        rowEvaluation (∐ F) a =
      Limits.Sigma.map (fun i ↦ rowEvaluation (F i) a) ≫
        sigmaComparison (postcompose SSet.π₀Functor) F := by
  apply Limits.Sigma.hom_ext
  intro i
  have hn : (postcompose (ihom K ⋙ SSet.π₀Functor)).map (Limits.Sigma.ι F i) ≫
      rowEvaluation (∐ F) a =
        rowEvaluation (F i) a ≫ (postcompose SSet.π₀Functor).map (Limits.Sigma.ι F i) := by
    apply NatTrans.ext
    funext h q
    change SSet.mapπ₀ (pointEvaluation a _)
      (SSet.mapπ₀ ((ihom K).map ((Limits.Sigma.ι F i).app h)) q) =
        SSet.mapπ₀ ((Limits.Sigma.ι F i).app h) (SSet.mapπ₀ (pointEvaluation a _) q)
    rw [← SSet.mapπ₀_comp_apply, pointEvaluation_natural, SSet.mapπ₀_comp_apply]
  simp only [← Category.assoc]
  rw [ι_comp_sigmaComparison, Limits.Sigma.ι_map]
  apply hn.trans
  rw [Category.assoc]
  exact congrArg (fun k ↦ rowEvaluation (F i) a ≫ k)
    (ι_comp_sigmaComparison (postcompose SSet.π₀Functor) F i).symm

def evaluationArrowIso {I : Type u} (F : I → BiSSet.{u}) {K : SSet.{u}}
    [Subsingleton K.π₀] (v : K _⦋0⦌) (a : 𝟙_ SSet.{u} ⟶ K) :
    Arrow.mk (Limits.Sigma.map (fun i ↦ rowEvaluation (F i) a)) ≅
      Arrow.mk (rowEvaluation (∐ F) a) := by
  have := preserves_coproducts K v I
  have : PreservesColimitsOfShape (Discrete I) (ihom K ⋙ SSet.π₀Functor) := inferInstance
  exact Arrow.isoMk (whiskerSigmaIso (ihom K ⋙ SSet.π₀Functor) F)
    (whiskerSigmaIso SSet.π₀Functor F) (by
      change sigmaComparison (postcompose (ihom K ⋙ SSet.π₀Functor)) F ≫ _ =
        _ ≫ sigmaComparison (postcompose SSet.π₀Functor) F
      exact evaluation_comparison_square F a)

theorem coproduct_evaluation_fibration {I : Type u} (F : I → BiSSet.{u})
    {K : SSet.{u}} [Subsingleton K.π₀] (v : K _⦋0⦌) (a : 𝟙_ SSet.{u} ⟶ K)
    [∀ i, Fibration (C := SSet.{u}) (rowEvaluation (F i) a)] :
    Fibration (C := SSet.{u}) (rowEvaluation (∐ F) a) := by
  have hp : Fibration (C := SSet.{u}) (Limits.Sigma.map (fun i ↦ rowEvaluation (F i) a)) :=
    sigma_map_fibration _
  exact (fibration_iff (C := SSet.{u}) _).mpr
    (((fibrations SSet.{u}).arrow_mk_iso_iff (evaluationArrowIso F v a)).mp
      ((fibration_iff (C := SSet.{u}) _).mp hp))

end
end DaggerNativeCoproductEvaluationFibration
