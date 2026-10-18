import OriginalGateChainHomDiagram
import OriginalGateNecklaceDiagram

set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial
open DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode
open DaggerOriginalFlagFlankification

universe u

namespace DaggerOriginalProductGadget

noncomputable section

variable {X : SSet.{u}}
  (R : X.obj (op ⦋0⦌) → X.obj (op ⦋0⦌) → Prop)
  (hrefl : ∀ x, R x x)
  (htrans : ∀ {x y z}, R x y → R y z → R x z)
  (hanti : ∀ {x y}, R x y → R y x → x = y)
  (hbound : ∀ {a b} {q : SimplexCategoryᵒᵖ} (x : (flagHom X a b).obj q) w,
    w ∈ flagVertexSupport x → R a w ∧ R w b)
  (hm : ∀ {a b} (P : NecklacesOver X a b),
    (∀ c : P.code.Bead, beadElement P c ∈ X.nonDegenerate c.length) → Mono P.map)
  (a b : X.obj (op ⦋0⦌)) (A : Set (X.obj (op ⦋0⦌)))

/-- Reuse the actual monomorphic-necklace colimit presentation to obtain the full Hom diagram. -/
def monicGateHomDiagramIso : monicGateColimitDiagram a b A R ≅
    gateChainHomDiagram R hrefl htrans hanti hbound hm a b A :=
  monicGateDiagramIso a b A R hm ≪≫
    gateChainDiagramIso R hrefl htrans hanti hbound hm a b A

/-- The necklace-colimit diagram comparison retains the original Hom augmentation. -/
theorem monicGateHomDiagramIso_augmentation (S : FlagGateIndex A R) :
    (monicGateHomDiagramIso R hrefl htrans hanti hbound hm a b A).hom.app S ≫
      (gateChainHomCocone R hrefl htrans hanti hbound hm a b A).ι.app S =
        (monicGateColimitCocone a b A R).ι.app S := by
  change ((monicGateDiagramIso a b A R hm).hom.app S ≫
    (gateChainDiagramIso R hrefl htrans hanti hbound hm a b A).hom.app S) ≫ _ = _
  rw [Category.assoc, gateChainDiagramIso_augmentation, monicGateDiagramIso_augmentation]

/-- The literal binary target supplies the entire necklace-colimit to original-Hom diagram iso. -/
def productCutMonicGateHomDiagramIso (n : ℕ) (factor : Fin n → NecklaceCode) (T : NecklaceCode)
    (a b : (productSpace.{u} n factor ⨯ T.toSSet).obj (op ⦋0⦌))
    (A : Set ((productSpace n factor ⨯ T.toSSet).obj (op ⦋0⦌))) :=
  monicGateHomDiagramIso (productCutVertexLE n factor T) (productCutVertexLE_refl n factor T)
    (productCutVertexLE_trans n factor T) (productCutVertexLE_antisymm n factor T)
    (productCut_support_bounds n factor T) (productCut_necklace_mono_of_nondegenerate n factor T)
    a b A

end

end DaggerOriginalProductGadget
