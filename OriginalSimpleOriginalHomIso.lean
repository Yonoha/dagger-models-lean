import OriginalSimpleFlagHomIso
import OriginalProductNecklaceCut
import ChosenFlagOriginalHomNaturality

set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial
open DaggerChosenRigidificationNecklace DaggerChosenRigidificationNecklace.NecklaceCode

universe u

namespace DaggerOriginalProductGadget

noncomputable section

variable {A X : SSet.{u}} (j : A ⟶ X) (hj : NecklaceSimple j) [Mono j]

/-- The same original enriched Hom, with both endpoint transports, is preserved by the inclusion. -/
def simpleOriginalHomIso (a b : A.obj (op ⦋0⦌)) :
    (RV A a ⟶[SSet.{u}] RV A b) ≅ (RV X (j.app _ a) ⟶[SSet.{u}] RV X (j.app _ b)) :=
  ((flagOriginalHomIso A a b).symm ≪≫ simpleFlagHomIso j hj) ≪≫
    flagOriginalHomIso X (j.app _ a) (j.app _ b)

theorem simpleOriginalHomIso_hom (a b : A.obj (op ⦋0⦌)) :
    (simpleOriginalHomIso j hj a b).hom = originalChosenHomMap j a b := by
  change ((flagOriginalHomIso A a b).inv ≫ flagHomMap j) ≫
    (flagOriginalHomIso X (j.app _ a) (j.app _ b)).hom = _
  rw [Category.assoc, flagOriginalHomIso_naturality, Iso.inv_hom_id_assoc]

include hj in
theorem simpleOriginalHomMap_isIso (a b : A.obj (op ⦋0⦌)) :
    IsIso (originalChosenHomMap j a b) := by
  rw [← simpleOriginalHomIso_hom j hj a b]
  infer_instance

end

noncomputable section

/-- Both endpoints on the left side retain the literal original Hom map into the full product. -/
theorem productCutLeft_originalHom_isIso (K : SSet.{u}) (T : NecklaceCode)
    (v : Fin (T.len + 1)) (a b : (K ⨯ (cutLeft T v).toSSet).obj (op ⦋0⦌)) :
    IsIso (originalChosenHomMap (prod.map (𝟙 K) (cutLeftι T v)) a b) := by
  have : Mono (prod.map (𝟙 K) (cutLeftι T v)) := (productCut_mono K T v).2.2.1
  exact simpleOriginalHomMap_isIso _ (productCut_necklaceSimple K T v).2.2.1 a b

/-- Both endpoints on the right side retain the literal original Hom map into the full product. -/
theorem productCutRight_originalHom_isIso (K : SSet.{u}) (T : NecklaceCode)
    (v : Fin (T.len + 1)) (a b : (K ⨯ (cutRight T v).toSSet).obj (op ⦋0⦌)) :
    IsIso (originalChosenHomMap (prod.map (𝟙 K) (cutRightι T v)) a b) := by
  have : Mono (prod.map (𝟙 K) (cutRightι T v)) := (productCut_mono K T v).2.2.2
  exact simpleOriginalHomMap_isIso _ (productCut_necklaceSimple K T v).2.2.2 a b

end

end DaggerOriginalProductGadget
