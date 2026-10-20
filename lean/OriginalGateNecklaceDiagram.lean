import OriginalGateNecklaceIso
import OriginalFlagGateDiagram

set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial
open DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode
open DaggerOriginalFlagFlankification

universe u

namespace DaggerOriginalProductGadget

noncomputable section

variable {X : SSet.{u}} (a b : X.obj (op ⦋0⦌)) (A : Set (X.obj (op ⦋0⦌)))
  (R : X.obj (op ⦋0⦌) → X.obj (op ⦋0⦌) → Prop)

/-- The paper's gate-indexed diagram of colimits over actual monomorphic necklaces. -/
def monicGateColimitDiagram : FlagGateIndex A R ⥤ SSet.{u} where
  obj S := monicGateHom a b S.val
  map f := monicGateTransition (leOfHom f)
  map_id S := by
    ext q x
    induction x using Quot.ind with | _ x
    rfl
  map_comp f g := by
    ext q x
    induction x using Quot.ind with | _ x
    rfl

/-- The entire original gate diagram, not only its objectwise sets, has the necklace presentation. -/
def monicGateDiagramIso
    (hm : ∀ P : NecklacesOver X a b,
      (∀ c : P.code.Bead, beadElement P c ∈ X.nonDegenerate c.length) → Mono P.map) :
    monicGateColimitDiagram a b A R ≅ flagGateDiagram a b A R :=
  NatIso.ofComponents (fun S ↦ monicGateIso S.val hm)
    (fun f ↦ monicGateIso_naturality hm (leOfHom f))

/-- The original Hom cocone on the necklace-colimit diagram. -/
def monicGateColimitCocone : Cocone (monicGateColimitDiagram a b A R) where
  pt := flagHom X a b
  ι :=
    { app S := monicGateToHom a b S.val
      naturality S T f := by
        ext q x
        induction x using Quot.ind with | _ x
        rfl }

/-- The diagram isomorphism preserves the specified augmentation to the original Hom. -/
theorem monicGateDiagramIso_augmentation
    (hm : ∀ P : NecklacesOver X a b,
      (∀ c : P.code.Bead, beadElement P c ∈ X.nonDegenerate c.length) → Mono P.map)
    (S : FlagGateIndex A R) :
    (monicGateDiagramIso a b A R hm).hom.app S ≫ (flagGateCocone a b A R).ι.app S =
      (monicGateColimitCocone a b A R).ι.app S := rfl

/-- Specialization to the actual binary target discharges the ordered-target hypothesis. -/
def productCutGateDiagramIso (n : ℕ) (factor : Fin n → NecklaceCode) (T : NecklaceCode)
    (a b : (productSpace.{u} n factor ⨯ T.toSSet).obj (op ⦋0⦌))
    (A : Set ((productSpace n factor ⨯ T.toSSet).obj (op ⦋0⦌)))
    (R : (productSpace n factor ⨯ T.toSSet).obj (op ⦋0⦌) →
      (productSpace n factor ⨯ T.toSSet).obj (op ⦋0⦌) → Prop) :
    monicGateColimitDiagram a b A R ≅ flagGateDiagram a b A R :=
  monicGateDiagramIso a b A R (productCut_necklace_mono_of_nondegenerate n factor T)

end

end DaggerOriginalProductGadget
