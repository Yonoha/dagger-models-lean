import ChosenFlagChosenHomCocone
import ChosenNecklaceWedgePathValues
import ChosenNecklacesOverWedge

open CategoryTheory EnrichedCategory MonoidalCategory Opposite Simplicial

universe u

namespace DaggerChosenRigidificationNecklace

noncomputable section

open NecklaceCode NecklaceThickening

variable {X : SSet.{u}} {a b c : X.obj (op ⦋0⦌)}
variable (P : NecklacesOver X a b) (Q : NecklacesOver X b c)

theorem overChosenFunctor_wedge_left :
    wedgeNCLeft P.code Q.code ≫ overChosenFunctor (NecklacesOver.wedge P Q) =
      overChosenFunctor P := by
  unfold wedgeNCLeft overChosenFunctor
  change generalNCMap (wedgeιLeft P.code Q.code) ≫
      ((chosenNecklaceIso (wedge P.code Q.code)).inv ≫
        C.map (NecklacesOver.wedge P Q).map) = _
  rw [← Category.assoc, chosenNecklaceIso_inv_naturality (wedgeιLeft P.code Q.code),
    Category.assoc,
    ← C.map_comp, NecklacesOver.wedge_left]

theorem overChosenFunctor_wedge_right :
    wedgeNCRight P.code Q.code ≫ overChosenFunctor (NecklacesOver.wedge P Q) =
      overChosenFunctor Q := by
  unfold wedgeNCRight overChosenFunctor
  change generalNCMap (wedgeιRight P.code Q.code) ≫
      ((chosenNecklaceIso (wedge P.code Q.code)).inv ≫
        C.map (NecklacesOver.wedge P Q).map) = _
  rw [← Category.assoc, chosenNecklaceIso_inv_naturality (wedgeιRight P.code Q.code),
    Category.assoc,
    ← C.map_comp, NecklacesOver.wedge_right]

def wedgeChosenFirst :
    (overChosenFunctor (NecklacesOver.wedge P Q)).obj
      ((wedgeNCLeft P.code Q.code).obj (outerLeft P.code)) = RV X a :=
  (congrArg (fun F ↦ F.obj (outerLeft P.code))
    (overChosenFunctor_wedge_left P Q)).trans (overChosenFunctor_first P)

def wedgeChosenJoint :
    (overChosenFunctor (NecklacesOver.wedge P Q)).obj
      ((wedgeNCLeft P.code Q.code).obj (outerRight P.code)) = RV X b :=
  (congrArg (fun F ↦ F.obj (outerRight P.code))
    (overChosenFunctor_wedge_left P Q)).trans (overChosenFunctor_last P)

def wedgeChosenLast :
    (overChosenFunctor (NecklacesOver.wedge P Q)).obj
      ((wedgeNCRight P.code Q.code).obj (outerRight Q.code)) = RV X c :=
  (congrArg (fun F ↦ F.obj (outerRight Q.code))
    (overChosenFunctor_wedge_right P Q)).trans (overChosenFunctor_last Q)

/-- Whole left Hom leg, preserving the supplied P and its two original endpoint equations. -/
theorem chosenFlagLeg_wedge_left :
    (outerFlagIso P.code).hom ≫
      (wedgeNCLeft P.code Q.code).map (outerLeft P.code) (outerRight P.code) ≫
      (overChosenFunctor (NecklacesOver.wedge P Q)).map _ _ ≫
      targetHomTransport (wedgeChosenFirst P Q) (wedgeChosenJoint P Q) =
        chosenFlagLeg P := by
  have H := enrichedFunctor_hom_congr_to_fixed (overChosenFunctor_wedge_left P Q)
    (outerLeft P.code) (outerRight P.code) (RV X a) (RV X b)
    (wedgeChosenFirst P Q) (wedgeChosenJoint P Q)
    (overChosenFunctor_first P) (overChosenFunctor_last P)
  change (outerFlagIso P.code).hom ≫
    ((wedgeNCLeft P.code Q.code ≫ overChosenFunctor (NecklacesOver.wedge P Q)).map
      (outerLeft P.code) (outerRight P.code) ≫
      targetHomTransport (wedgeChosenFirst P Q) (wedgeChosenJoint P Q)) = _
  rw [H]
  rfl

/-- Whole right Hom leg with the original equality of the glued vertices. -/
theorem chosenFlagLeg_wedge_right :
    (outerFlagIso Q.code).hom ≫
      (wedgeNCRight P.code Q.code).map (outerLeft Q.code) (outerRight Q.code) ≫
      targetHomTransport (wedgeNC_joint P.code Q.code).symm rfl ≫
      (overChosenFunctor (NecklacesOver.wedge P Q)).map _ _ ≫
      targetHomTransport (wedgeChosenJoint P Q) (wedgeChosenLast P Q) =
        chosenFlagLeg Q := by
  rw [← Category.assoc (targetHomTransport (wedgeNC_joint P.code Q.code).symm rfl),
    enriched_map_endpoint_transport, Category.assoc, targetHomTransport_trans]
  have hx := (congrArg (overChosenFunctor (NecklacesOver.wedge P Q)).obj
    (wedgeNC_joint P.code Q.code).symm).trans (wedgeChosenJoint P Q)
  have H := enrichedFunctor_hom_congr_to_fixed (overChosenFunctor_wedge_right P Q)
    (outerLeft Q.code) (outerRight Q.code) (RV X b) (RV X c)
    hx (wedgeChosenLast P Q) (overChosenFunctor_first Q) (overChosenFunctor_last Q)
  change (outerFlagIso Q.code).hom ≫
    ((wedgeNCRight P.code Q.code ≫ overChosenFunctor (NecklacesOver.wedge P Q)).map
      (outerLeft Q.code) (outerRight Q.code) ≫
      targetHomTransport hx (wedgeChosenLast P Q)) = _
  rw [H]
  rfl

end

end DaggerChosenRigidificationNecklace
