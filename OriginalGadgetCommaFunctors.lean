import OriginalGadgetsOver

set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial
open DaggerChosenRigidificationNecklace

universe u

namespace DaggerOriginalProductGadget

noncomputable section

variable {X : SSet.{u}} {a b : X.obj (op ⦋0⦌)} (Q : GadgetsOver X a b)

/-- The genuine comma category of the singleton inclusion over the supplied original gadget. -/
abbrev GadgetComma := CostructuredArrow (gadgetSingleton X a b) Q

/-- Remove the one-factor presentation, retaining the original realization map. -/
def gadgetCommaNecklaceObj (P : GadgetComma Q) :
    NecklacesOver Q.obj.left.space Q.obj.left.alpha Q.obj.left.omega where
  code := P.left.code
  map := (singletonSpaceIso P.left.code).inv ≫ P.hom.hom.left.map
  first := by
    change P.hom.hom.left.map.app _ ((singletonSpaceIso P.left.code).inv.app _ P.left.code.first)
      = Q.obj.left.alpha
    rw [singletonSpaceIso_inv_alpha]
    exact P.hom.hom.left.alpha
  last := by
    change P.hom.hom.left.map.app _ ((singletonSpaceIso P.left.code).inv.app _ P.left.code.last)
      = Q.obj.left.omega
    rw [singletonSpaceIso_inv_omega]
    exact P.hom.hom.left.omega

/-- Every comma morphism is the same original necklace morphism over the gadget realization. -/
def gadgetCommaToNecklaces :
    GadgetComma Q ⥤ NecklacesOver Q.obj.left.space Q.obj.left.alpha Q.obj.left.omega where
  obj := gadgetCommaNecklaceObj Q
  map {P R} h :=
    { hom := h.left.hom
      w := by
        have hw := congrArg (fun z : (gadgetSingleton X a b).obj P.left ⟶ Q ↦ z.hom.left.map)
          (CostructuredArrow.w h)
        change ((singletonSpaceIso P.left.code).hom ≫ h.left.hom.map ≫
          (singletonSpaceIso R.left.code).inv) ≫ R.hom.hom.left.map = P.hom.hom.left.map at hw
        have hh := congrArg (fun z ↦ (singletonSpaceIso P.left.code).inv ≫ z) hw
        simpa only [Category.assoc, Iso.inv_hom_id_assoc] using hh }
  map_id P := by
    apply NecklacesOver.Hom.ext
    rfl
  map_comp h k := by
    apply NecklacesOver.Hom.ext
    rfl

/-- Postcompose an actual necklace over the gadget with its supplied map to X. -/
def gadgetNecklaceOverObj
    (P : NecklacesOver Q.obj.left.space Q.obj.left.alpha Q.obj.left.omega) :
    NecklacesOver X a b where
  code := P.code
  map := P.map ≫ Q.obj.hom
  first := by
    change Q.obj.hom.app _ (P.map.app _ P.code.first) = a
    rw [P.first]
    exact Q.property.1
  last := by
    change Q.obj.hom.app _ (P.map.app _ P.code.last) = b
    rw [P.last]
    exact Q.property.2

/-- The original over-gadget map defines its actual arrow from a singleton gadget. -/
def gadgetNecklaceArrow
    (P : NecklacesOver Q.obj.left.space Q.obj.left.alpha Q.obj.left.omega) :
    (gadgetSingleton X a b).obj (gadgetNecklaceOverObj Q P) ⟶ Q :=
  ObjectProperty.homMk (CostructuredArrow.homMk
    ({ map := (singletonSpaceIso P.code).hom ≫ P.map
       alpha := by
         change P.map.app _ ((singletonSpaceIso P.code).hom.app _ (singleton P.code).alpha) = _
         rw [singletonSpaceIso_alpha, P.first]
       omega := by
         change P.map.app _ ((singletonSpaceIso P.code).hom.app _ (singleton P.code).omega) = _
         rw [singletonSpaceIso_omega, P.last] } : Hom (singleton P.code) Q.obj.left)
    (by exact Category.assoc _ _ _))

/-- Insert the original over-gadget necklace into Mathlib's actual comma category. -/
def gadgetNecklacesToComma :
    NecklacesOver Q.obj.left.space Q.obj.left.alpha Q.obj.left.omega ⥤ GadgetComma Q where
  obj P := CostructuredArrow.mk (gadgetNecklaceArrow Q P)
  map {P R} h := CostructuredArrow.homMk
    ({ hom := h.hom
       w := by
         change h.hom.map ≫ (R.map ≫ Q.obj.hom) = P.map ≫ Q.obj.hom
         rw [← Category.assoc, h.w] } : gadgetNecklaceOverObj Q P ⟶ gadgetNecklaceOverObj Q R)
    (by
      apply ObjectProperty.hom_ext
      apply CostructuredArrow.hom_ext
      apply Hom.ext
      change ((singletonSpaceIso P.code).hom ≫ h.hom.map ≫ (singletonSpaceIso R.code).inv) ≫
        ((singletonSpaceIso R.code).hom ≫ R.map) = (singletonSpaceIso P.code).hom ≫ P.map
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      rw [h.w])
  map_id P := by
    apply CostructuredArrow.hom_ext
    apply NecklacesOver.Hom.ext
    rfl
  map_comp h k := by
    apply CostructuredArrow.hom_ext
    apply NecklacesOver.Hom.ext
    rfl

theorem gadgetCommaToNecklaces_map (P : GadgetComma Q) :
    ((gadgetCommaToNecklaces Q).obj P).map =
      (singletonSpaceIso P.left.code).inv ≫ P.hom.hom.left.map := rfl

theorem gadgetNecklacesToComma_map
    (P : NecklacesOver Q.obj.left.space Q.obj.left.alpha Q.obj.left.omega) :
    ((gadgetNecklacesToComma Q).obj P).hom.hom.left.map =
      (singletonSpaceIso P.code).hom ≫ P.map := rfl

/-- The reconstructed necklace keeps the entire original map to X. -/
theorem gadgetComma_original_map (P : GadgetComma Q) :
    ((gadgetCommaToNecklaces Q).obj P).map ≫ Q.obj.hom = P.left.map := by
  have hw := CostructuredArrow.w P.hom.hom
  change P.hom.hom.left.map ≫ Q.obj.hom = (singletonSpaceIso P.left.code).hom ≫ P.left.map at hw
  change ((singletonSpaceIso P.left.code).inv ≫ P.hom.hom.left.map) ≫ Q.obj.hom = _
  rw [Category.assoc, hw, Iso.inv_hom_id_assoc]

end

end DaggerOriginalProductGadget
