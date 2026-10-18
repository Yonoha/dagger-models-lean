import OriginalGadgetsOver
import OriginalNerveProduct

set_option autoImplicit false
open CategoryTheory MonoidalCategory CartesianMonoidalCategory Opposite Simplicial
open DaggerOriginalNerveProduct

universe u

namespace DaggerOriginalProductGadget

noncomputable section

variable {X Y : SSet.{u}} (a b : X.obj (op ⦋0⦌)) (c d : Y.obj (op ⦋0⦌))

/-- Both projections keep the supplied gadget and postcompose its original map. -/
def gadgetPhi : GadgetsOver (X ⊗ Y) (a, c) (b, d) ⥤
    GadgetsOver X a b × GadgetsOver Y c d :=
  (gadgetPostcomp (fst X Y)).prod' (gadgetPostcomp (snd X Y))

theorem gadgetPhi_obj_fst (P : GadgetsOver (X ⊗ Y) (a, c) (b, d)) :
    ((gadgetPhi a b c d).obj P).1.obj.hom = P.obj.hom ≫ fst X Y := rfl

theorem gadgetPhi_obj_snd (P : GadgetsOver (X ⊗ Y) (a, c) (b, d)) :
    ((gadgetPhi a b c d).obj P).2.obj.hom = P.obj.hom ≫ snd X Y := rfl

theorem gadgetPhi_obj_codes (P : GadgetsOver (X ⊗ Y) (a, c) (b, d)) :
    ((gadgetPhi a b c d).obj P).1.obj.left = P.obj.left ∧
      ((gadgetPhi a b c d).obj P).2.obj.left = P.obj.left := ⟨rfl, rfl⟩

theorem gadgetPhi_map_fst {P Q : GadgetsOver (X ⊗ Y) (a, c) (b, d)} (h : P ⟶ Q) :
    ((gadgetPhi a b c d).map h).1.hom.left.map = h.hom.left.map := rfl

theorem gadgetPhi_map_snd {P Q : GadgetsOver (X ⊗ Y) (a, c) (b, d)} (h : P ⟶ Q) :
    ((gadgetPhi a b c d).map h).2.hom.left.map = h.hom.left.map := rfl

/-- The comparison to the actual simplicial product, using Mathlib's nerve product iso. -/
def nerveGadgetPhi : nerve (GadgetsOver (X ⊗ Y) (a, c) (b, d)) ⟶
    nerve (GadgetsOver X a b) ⊗ nerve (GadgetsOver Y c d) :=
  nerveMap (gadgetPhi a b c d) ≫
    (nerveProductIso (GadgetsOver X a b) (GadgetsOver Y c d)).hom

theorem nerveGadgetPhi_fst : nerveGadgetPhi a b c d ≫ fst _ _ =
    nerveMap (gadgetPostcomp (a := (a, c)) (b := (b, d)) (fst X Y)) := by
  unfold nerveGadgetPhi
  rw [Category.assoc, nerveProductIso_hom_fst]
  exact (nerveFunctor.map_comp (gadgetPhi a b c d).toCatHom
    (CategoryTheory.Prod.fst (GadgetsOver X a b) (GadgetsOver Y c d)).toCatHom).symm

theorem nerveGadgetPhi_snd : nerveGadgetPhi a b c d ≫ snd _ _ =
    nerveMap (gadgetPostcomp (a := (a, c)) (b := (b, d)) (snd X Y)) := by
  unfold nerveGadgetPhi
  rw [Category.assoc, nerveProductIso_hom_snd]
  exact (nerveFunctor.map_comp (gadgetPhi a b c d).toCatHom
    (CategoryTheory.Prod.snd (GadgetsOver X a b) (GadgetsOver Y c d)).toCatHom).symm

theorem nerveGadgetPhi_eq_lift : nerveGadgetPhi a b c d =
    CartesianMonoidalCategory.lift
      (nerveMap (gadgetPostcomp (a := (a, c)) (b := (b, d)) (fst X Y)))
      (nerveMap (gadgetPostcomp (a := (a, c)) (b := (b, d)) (snd X Y))) := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [nerveGadgetPhi_fst]
    exact (CartesianMonoidalCategory.lift_fst _ _).symm
  · rw [nerveGadgetPhi_snd]
    exact (CartesianMonoidalCategory.lift_snd _ _).symm

end

end DaggerOriginalProductGadget
