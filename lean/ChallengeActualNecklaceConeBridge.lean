import ActualNecklaceConeGadgets
import ActualRightConeGadgetIndex
import OriginalFlagP2CompleteReconciledRecovered
import ChosenFlagOriginalHomIso
import OriginalProductBeadFlagCollapseReconciledRecovered

/-! Problem statement for the actual common-gadget bridge, with literal original P2 legs.
Only gadget/index data and existing problem definitions are imported. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial
open DaggerModels
open DaggerChosenRigidificationNecklace hiding SimplexIndex
open DaggerNerveHomotopy DaggerBisimplicialDiagonal
open DaggerOriginalFlagFlankification DaggerSSetGluing
open DaggerActualNecklaceConeGadgets
open DaggerOriginalProductGadget hiding Code
open DaggerOriginalCounitBNextConeEvaluationIndex
open DaggerOriginalCounitRightConeQRealizationAdjunction
universe u

namespace DaggerActualNecklaceConeBridgeChallenge

def statement : Prop :=
  (∀ (X : SSet.{u}) (a b : X.obj (op ⦋0⦌)),
    GW (nerveMap (inclusion X a b)) ∧
    (∀ Q : Over X a b, GW (pointMap (nerve (Comma Q)))) ∧
    GW (originalEpsilon X a b ≫ (flagOriginalHomIso X a b).hom) ∧
    GW (originalPi X a b ≫ nerveMap (inclusion X a b))) ∧
  (∀ (D : SimplicialCat.{u, u})
    (v w : (DaggerModels.OrdinaryRigidification.coherentNerve.obj D).obj (op ⦋0⦌))
    (σ : SimplexIndex (rightConeSimplices D v w)),
    ((DaggerActualRightConeGadgetIndex.index D v w).obj σ).map =
      (uliftYonedaEquiv σ.hom).val) ∧
  (∀ (D : SimplicialCat.{u, u})
    (v w : (DaggerModels.OrdinaryRigidification.coherentNerve.obj D).obj (op ⦋0⦌))
    (σ τ : SimplexIndex (rightConeSimplices D v w)) (f : σ ⟶ τ),
    ((DaggerActualRightConeGadgetIndex.index D v w).map f).hom.map =
      DaggerOriginalCounitRightConeFunctor.coneMap.{u} f.left)

end DaggerActualNecklaceConeBridgeChallenge
