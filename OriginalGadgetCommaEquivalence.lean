import OriginalGadgetCommaFunctors
import Mathlib.CategoryTheory.Equivalence

set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial
open DaggerChosenRigidificationNecklace

universe u

namespace DaggerOriginalProductGadget

noncomputable section

variable {X : SSet.{u}} {a b : X.obj (op ⦋0⦌)} (Q : GadgetsOver X a b)

/-- The necklace roundtrip retains its code and is the identity on that code. -/
def gadgetNecklaceRoundtripIso
    (P : NecklacesOver Q.obj.left.space Q.obj.left.alpha Q.obj.left.omega) :
    (gadgetCommaToNecklaces Q).obj ((gadgetNecklacesToComma Q).obj P) ≅ P where
  hom :=
    { hom := 𝟙 P.code
      w := by
        change 𝟙 _ ≫ P.map = (singletonSpaceIso P.code).inv ≫
          ((singletonSpaceIso P.code).hom ≫ P.map)
        simp }
  inv :=
    { hom := 𝟙 P.code
      w := by
        change 𝟙 _ ≫ ((singletonSpaceIso P.code).inv ≫
          ((singletonSpaceIso P.code).hom ≫ P.map)) = P.map
        simp }
  hom_inv_id := by
    apply NecklacesOver.Hom.ext
    apply NecklaceCode.Hom.ext
    change 𝟙 (P.code.toSSet : SSet.{u}) ≫ 𝟙 _ = 𝟙 _
    simp
  inv_hom_id := by
    apply NecklacesOver.Hom.ext
    apply NecklaceCode.Hom.ext
    change 𝟙 (P.code.toSSet : SSet.{u}) ≫ 𝟙 _ = 𝟙 _
    simp

/-- Both directions of the necklace roundtrip are natural for every original necklace map. -/
def gadgetNecklaceRoundtrip : gadgetNecklacesToComma Q ⋙ gadgetCommaToNecklaces Q ≅ 𝟭 _ :=
  NatIso.ofComponents (gadgetNecklaceRoundtripIso Q) (by
    intro P R h
    apply NecklacesOver.Hom.ext
    apply NecklaceCode.Hom.ext
    change h.hom.map ≫ 𝟙 _ = 𝟙 _ ≫ h.hom.map
    simp)

/-- The comma roundtrip recovers the whole over-X necklace, not just its source code. -/
def gadgetCommaLeftRoundtripIso (P : GadgetComma Q) :
    ((gadgetNecklacesToComma Q).obj ((gadgetCommaToNecklaces Q).obj P)).left ≅ P.left where
  hom :=
    { hom := 𝟙 P.left.code
      w := by
        change 𝟙 _ ≫ P.left.map = ((gadgetCommaToNecklaces Q).obj P).map ≫ Q.obj.hom
        rw [Category.id_comp, gadgetComma_original_map] }
  inv :=
    { hom := 𝟙 P.left.code
      w := by
        change 𝟙 _ ≫ (((gadgetCommaToNecklaces Q).obj P).map ≫ Q.obj.hom) = P.left.map
        rw [Category.id_comp, gadgetComma_original_map] }
  hom_inv_id := by
    apply NecklacesOver.Hom.ext
    apply NecklaceCode.Hom.ext
    change 𝟙 (P.left.code.toSSet : SSet.{u}) ≫ 𝟙 _ = 𝟙 _
    simp
  inv_hom_id := by
    apply NecklacesOver.Hom.ext
    apply NecklaceCode.Hom.ext
    change 𝟙 (P.left.code.toSSet : SSet.{u}) ≫ 𝟙 _ = 𝟙 _
    simp

/-- Mathlib's comma isomorphism retains the complete original arrow to the supplied gadget. -/
def gadgetCommaRoundtripIso (P : GadgetComma Q) :
    (gadgetNecklacesToComma Q).obj ((gadgetCommaToNecklaces Q).obj P) ≅ P :=
  CostructuredArrow.isoMk (gadgetCommaLeftRoundtripIso Q P) (by
    apply ObjectProperty.hom_ext
    apply CostructuredArrow.hom_ext
    apply Hom.ext
    change ((singletonSpaceIso P.left.code).hom ≫ 𝟙 _ ≫
      (singletonSpaceIso P.left.code).inv) ≫ P.hom.hom.left.map =
      (singletonSpaceIso P.left.code).hom ≫
        ((singletonSpaceIso P.left.code).inv ≫ P.hom.hom.left.map)
    simp)

/-- The whole comma roundtrip is natural, including the original triangle equation. -/
def gadgetCommaRoundtrip : gadgetCommaToNecklaces Q ⋙ gadgetNecklacesToComma Q ≅ 𝟭 _ :=
  NatIso.ofComponents (gadgetCommaRoundtripIso Q) (by
    intro P R h
    apply CostructuredArrow.hom_ext
    apply NecklacesOver.Hom.ext
    apply NecklaceCode.Hom.ext
    change h.left.hom.map ≫ 𝟙 _ = 𝟙 _ ≫ h.left.hom.map
    simp)

/-- The actual comma category is equivalent to necklaces over the same gadget realization. -/
def gadgetCommaEquivalence :
    GadgetComma Q ≌ NecklacesOver Q.obj.left.space Q.obj.left.alpha Q.obj.left.omega :=
  CategoryTheory.Equivalence.mk (gadgetCommaToNecklaces Q) (gadgetNecklacesToComma Q)
    (gadgetCommaRoundtrip Q).symm (gadgetNecklaceRoundtrip Q)

/-- Postcomposition commutes with the original singleton inclusion through actual identity codes. -/
def gadgetSingletonPostcompIso {Y : SSet.{u}} (f : X ⟶ Y) :
    NecklacesOver.postcomp (a := a) (b := b) f ⋙
        gadgetSingleton Y (f.app _ a) (f.app _ b) ≅
      gadgetSingleton X a b ⋙ gadgetPostcomp f :=
  NatIso.ofComponents (fun P ↦ ObjectProperty.isoMk
    (gadgetEndpointProperty Y (f.app _ a) (f.app _ b)) (CostructuredArrow.isoMk
    (Iso.refl (singleton P.code)) (by
      change 𝟙 _ ≫ (((singletonSpaceIso P.code).hom ≫ P.map) ≫ f) =
        (singletonSpaceIso P.code).hom ≫ (P.map ≫ f)
      simp only [Category.id_comp, Category.assoc]))) (by
    intro P R h
    apply ObjectProperty.hom_ext
    apply CostructuredArrow.hom_ext
    change singletonFunctor.map h.hom ≫ 𝟙 _ = 𝟙 _ ≫ singletonFunctor.map h.hom
    simp)

end

end DaggerOriginalProductGadget
