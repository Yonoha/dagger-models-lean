import ActualInnerGadgetWeightedReindex
import ActualNecklaceFlagAugmentation
import NativeSimplicialReplacementWeightsChange

/-! The original necklace flag weights compare to the actual original endpoint-Hom weights. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial HomotopicalAlgebra DaggerModels OrdinaryRigidification
open DaggerChosenRigidificationNecklace DaggerOriginalFlagFlankification
open DaggerActualInnerGadgetHomAugmentation DaggerNativeSimplicialReplacement
open DaggerSSetGluing DaggerModels.OriginalOrdinaryMovingHomColimits
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerActualInnerNecklaceWeightComparison
noncomputable section

abbrev self (T : NecklaceCode) := DaggerActualNecklaceConeGadgetComparison.terminalNecklace T

/-- The full original self-necklace leg is the existing outer-Hom isomorphism. -/
theorem self_leg (T : NecklaceCode) : chosenFlagLeg (self T) =
    (necklaceOriginalOuterHomIso T).hom := by
  have hF : overChosenFunctor (self T) = (chosenNecklaceIso T).inv := by
    dsimp only [overChosenFunctor, self,
      DaggerActualNecklaceConeGadgetComparison.terminalNecklace]
    rw [CategoryTheory.Functor.map_id, Category.comp_id]
  rw [chosenFlagLeg, necklaceOriginalOuterHomIso_hom]
  apply congrArg (fun f ↦ (NecklaceThickening.outerFlagIso T).hom ≫ f)
  exact castMap_congr hF (NecklaceThickening.outerLeft T) (NecklaceThickening.outerRight T)
    (RV T.toSSet T.first) (RV T.toSSet T.last)
    (overChosenFunctor_first (self T)) (overChosenFunctor_last (self T))
    ((congrArg (fun F ↦ F.obj (NecklaceThickening.outerLeft T)) hF.symm).trans
      (overChosenFunctor_first (self T)))
    ((congrArg (fun F ↦ F.obj (NecklaceThickening.outerRight T)) hF.symm).trans
      (overChosenFunctor_last (self T)))

/-- The entire original flag leg factors through the original C(T) Hom and the full C(P.map). -/
theorem leg_factor {X : SSet.{u}} {a b : X.obj (op ⦋0⦌)} (P : NecklacesOver X a b) :
    (necklaceOriginalOuterHomIso P.code).hom ≫
      leg X a b ((DaggerActualInnerIteratedGadgetNecklaceComparison.inclusion X a b).obj P) =
        chosenFlagLeg P := by
  rw [← self_leg]
  change chosenFlagLeg (self P.code) ≫
    ((rigidification.map P.map).map (RV P.code.toSSet P.code.first)
      (RV P.code.toSSet P.code.last) ≫ targetHomTransport
        (original_source X a b
          ((DaggerActualInnerIteratedGadgetNecklaceComparison.inclusion X a b).obj P))
        (original_target X a b
          ((DaggerActualInnerIteratedGadgetNecklaceComparison.inclusion X a b).obj P))) =
      chosenFlagLeg P
  rw [chosenFlagLeg_image]
  have hF : overChosenFunctor (self P.code) ≫ rigidification.map P.map =
      overChosenFunctor P := by
    dsimp only [overChosenFunctor, self,
      DaggerActualNecklaceConeGadgetComparison.terminalNecklace]
    rw [CategoryTheory.Functor.map_id, Category.comp_id]
  rw [chosenFlagLeg]
  apply congrArg (fun f ↦ (NecklaceThickening.outerFlagIso P.code).hom ≫ f)
  exact castMap_congr hF (NecklaceThickening.outerLeft P.code)
    (NecklaceThickening.outerRight P.code) (RV X a) (RV X b)
    ((congrArg (fun F ↦ F.obj (NecklaceThickening.outerLeft P.code)) hF).trans
      (overChosenFunctor_first P))
    ((congrArg (fun F ↦ F.obj (NecklaceThickening.outerRight P.code)) hF).trans
      (overChosenFunctor_last P))
    (overChosenFunctor_first P) (overChosenFunctor_last P)

end
end DaggerActualInnerNecklaceWeightComparison
