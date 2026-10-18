import ChosenFlagChosenWedgeFunctor
import ChosenFlagEnrichment

open CategoryTheory EnrichedCategory MonoidalCategory Opposite Simplicial

universe u

namespace DaggerChosenRigidificationNecklace

noncomputable section

open NecklaceCode NecklaceThickening

variable {X : SSet.{u}} {a b c : X.obj (op ⦋0⦌)}

theorem chosenFlagLeg_wedge_raw (P : NecklacesOver X a b) (Q : NecklacesOver X b c)
    (q : SimplexCategoryᵒᵖ)
    (p : NecklaceCode.Flag.{u} P.code q.unop.len)
    (r : NecklaceCode.Flag.{u} Q.code q.unop.len) :
    (chosenFlagLeg (NecklacesOver.wedge P Q)).app q (NecklaceCode.Flag.wedge p r) =
      (eComp SSet (RV X a) (RV X b) (RV X c)).app q
        ((chosenFlagLeg P).app q p, (chosenFlagLeg Q).app q r) := by
  let W := NecklacesOver.wedge P Q
  let F := overChosenFunctor W
  let L := wedgeNCLeft P.code Q.code
  let R := wedgeNCRight P.code Q.code
  let x := L.obj (outerLeft P.code)
  let y := L.obj (outerRight P.code)
  let z := R.obj (outerRight Q.code)
  let l := (L.map (outerLeft P.code) (outerRight P.code)).app q
    ((outerFlagIso P.code).hom.app q p)
  let r' := (targetHomTransport (wedgeNC_joint P.code Q.code).symm rfl).app q
    ((R.map (outerLeft Q.code) (outerRight Q.code)).app q
      ((outerFlagIso Q.code).hom.app q r))
  have Hmap :
      targetHomTransport (wedgeNCLeft_first P.code Q.code)
          (wedgeNCRight_last P.code Q.code) ≫
        F.map (outerLeft (wedge P.code Q.code)) (outerRight (wedge P.code Q.code)) ≫
        targetHomTransport (overChosenFunctor_first W) (overChosenFunctor_last W) =
      F.map x z ≫ targetHomTransport (wedgeChosenFirst P Q) (wedgeChosenLast P Q) := by
    have HM := enriched_map_endpoint_transport
      (A := NC.{u} (wedge P.code Q.code)) (D := C.obj X) F
      (wedgeNCLeft_first P.code Q.code) (wedgeNCRight_last P.code Q.code)
    rw [← Category.assoc, HM]
    rw [Category.assoc, targetHomTransport_trans]
  have Hvalue := congrFun (NatTrans.congr_app Hmap q)
    ((eComp SSet x y z).app q (l, r'))
  have Hcomp := congrFun (NatTrans.congr_app
    (targetHomTransport_comp F x y z (RV X a) (RV X b) (RV X c)
      (wedgeChosenFirst P Q) (wedgeChosenJoint P Q) (wedgeChosenLast P Q)) q) (l, r')
  have HL := congrFun (NatTrans.congr_app (chosenFlagLeg_wedge_left P Q) q) p
  have HR := congrFun (NatTrans.congr_app (chosenFlagLeg_wedge_right P Q) q) r
  change (targetHomTransport (wedgeChosenFirst P Q) (wedgeChosenJoint P Q)).app q
    ((F.map x y).app q l) = (chosenFlagLeg P).app q p at HL
  change (targetHomTransport (wedgeChosenJoint P Q) (wedgeChosenLast P Q)).app q
    ((F.map y z).app q r') = (chosenFlagLeg Q).app q r at HR
  change (targetHomTransport (wedgeChosenFirst P Q) (wedgeChosenLast P Q)).app q
    ((F.map x z).app q ((eComp SSet x y z).app q (l, r'))) =
      (eComp SSet (RV X a) (RV X b) (RV X c)).app q
        ((targetHomTransport (wedgeChosenFirst P Q) (wedgeChosenJoint P Q)).app q
          ((F.map x y).app q l),
         (targetHomTransport (wedgeChosenJoint P Q) (wedgeChosenLast P Q)).app q
          ((F.map y z).app q r')) at Hcomp
  rw [HL, HR] at Hcomp
  change (targetHomTransport (overChosenFunctor_first W) (overChosenFunctor_last W)).app q
    ((F.map (outerLeft W.code) (outerRight W.code)).app q
      ((outerFlagIso W.code).hom.app q (NecklaceCode.Flag.wedge p r))) = _
  have HW := wedgeFlag_outer_comp P.code Q.code q p r
  have Houter := congrArg (fun t ↦
    (targetHomTransport (overChosenFunctor_first W) (overChosenFunctor_last W)).app q
      ((F.map (outerLeft W.code) (outerRight W.code)).app q t)) HW
  exact Houter.trans (Hvalue.trans Hcomp)

/-- All original ordered composites, including empty/point beads and diagonal endpoints. -/
theorem chosenFlagHom_composition (X : SSet.{u}) (a b c : X.obj (op ⦋0⦌)) :
    flagComposition X a b c ≫ chosenFlagHom X a c =
      (chosenFlagHom X a b ⊗ₘ chosenFlagHom X b c) ≫
        eComp SSet (RV X a) (RV X b) (RV X c) := by
  ext q v
  rcases v with ⟨v, w⟩
  induction v using Quot.ind with | _ p
  induction w using Quot.ind with | _ r
  exact chosenFlagLeg_wedge_raw p.1 r.1 q p.2 r.2

end

end DaggerChosenRigidificationNecklace
