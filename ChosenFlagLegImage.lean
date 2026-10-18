import ChosenFlagChosenHomCocone

open CategoryTheory EnrichedCategory MonoidalCategory Opposite Simplicial

universe u

namespace DaggerChosenRigidificationNecklace

noncomputable section

open NecklaceCode NecklaceThickening

variable {X : SSet.{u}} {a b : X.obj (op ⦋0⦌)}

/-- All target descent retains the same raw leg, with both endpoint transports displayed. -/
theorem chosenFlagLeg_image {D : DaggerModels.SimplicialCat.{u,u}}
    (P : NecklacesOver X a b) (F : C.obj X ⟶ D) (x y : D.Obj)
    (hx : F.obj (RV X a) = x) (hy : F.obj (RV X b) = y) :
    chosenFlagLeg P ≫ F.map (RV X a) (RV X b) ≫ targetHomTransport hx hy =
      (outerFlagIso P.code).hom ≫
        (overChosenFunctor P ≫ F).map (outerLeft P.code) (outerRight P.code) ≫
        targetHomTransport
          ((congrArg F.obj (overChosenFunctor_first P)).trans hx)
          ((congrArg F.obj (overChosenFunctor_last P)).trans hy) := by
  unfold chosenFlagLeg
  simp only [Category.assoc]
  rw [← Category.assoc (targetHomTransport (overChosenFunctor_first P)
    (overChosenFunctor_last P)), enriched_map_endpoint_transport]
  simp only [Category.assoc]
  rw [targetHomTransport_trans]
  rfl

end

end DaggerChosenRigidificationNecklace
