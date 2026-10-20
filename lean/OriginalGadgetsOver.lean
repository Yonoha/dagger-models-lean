import OriginalProductGadgetData
import ChosenNecklacesOver
import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial
open DaggerChosenRigidificationNecklace

universe u

namespace DaggerOriginalProductGadget

noncomputable section

/-- The two original endpoint equations inside Mathlib's actual costructured-arrow category. -/
def gadgetEndpointProperty (X : SSet.{u}) (a b : X.obj (op ⦋0⦌)) :
    ObjectProperty (CostructuredArrow realization.{u} X) :=
  fun P ↦ P.hom.app (op ⦋0⦌) P.left.alpha = a ∧ P.hom.app (op ⦋0⦌) P.left.omega = b

/-- All product gadgets over the supplied simplicial set, with all endpoint-preserving arrows. -/
abbrev GadgetsOver (X : SSet.{u}) (a b : X.obj (op ⦋0⦌)) :=
  (gadgetEndpointProperty X a b).FullSubcategory

/-- Embed an actual over-X necklace using the existing one-factor product isomorphism. -/
def gadgetSingletonObj {X : SSet.{u}} {a b : X.obj (op ⦋0⦌)} (P : NecklacesOver X a b) :
    GadgetsOver X a b :=
  ⟨CostructuredArrow.mk ((singletonSpaceIso P.code).hom ≫ P.map), by
    constructor
    · change P.map.app _ ((singletonSpaceIso P.code).hom.app _ (singleton P.code).alpha) = a
      rw [singletonSpaceIso_alpha, P.first]
    · change P.map.app _ ((singletonSpaceIso P.code).hom.app _ (singleton P.code).omega) = b
      rw [singletonSpaceIso_omega, P.last]⟩

/-- The original singleton inclusion includes every original necklace-over arrow. -/
def gadgetSingleton (X : SSet.{u}) (a b : X.obj (op ⦋0⦌)) :
    NecklacesOver X a b ⥤ GadgetsOver X a b where
  obj := gadgetSingletonObj
  map {P Q} h := ObjectProperty.homMk (CostructuredArrow.homMk
    (singletonFunctor.map h.hom) (by
      change ((singletonSpaceIso P.code).hom ≫ h.hom.map ≫ (singletonSpaceIso Q.code).inv) ≫
          ((singletonSpaceIso Q.code).hom ≫ Q.map) = (singletonSpaceIso P.code).hom ≫ P.map
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      rw [h.w]))
  map_id P := by
    apply ObjectProperty.hom_ext
    apply CostructuredArrow.hom_ext
    exact singletonFunctor.map_id P.code
  map_comp h k := by
    apply ObjectProperty.hom_ext
    apply CostructuredArrow.hom_ext
    exact singletonFunctor.map_comp h.hom k.hom

theorem gadgetSingleton_obj_map {X : SSet.{u}} {a b : X.obj (op ⦋0⦌)}
    (P : NecklacesOver X a b) :
    ((gadgetSingleton X a b).obj P).obj.hom = (singletonSpaceIso P.code).hom ≫ P.map := rfl

theorem gadgetSingleton_map_original {X : SSet.{u}} {a b : X.obj (op ⦋0⦌)}
    {P Q : NecklacesOver X a b} (h : P ⟶ Q) :
    ((gadgetSingleton X a b).map h).hom.left.map =
      (singletonSpaceIso P.code).hom ≫ h.hom.map ≫ (singletonSpaceIso Q.code).inv := rfl

/-- Postcomposition reuses Mathlib's functor on costructured arrows and keeps both endpoints. -/
def gadgetPostcomp {X Y : SSet.{u}} {a b : X.obj (op ⦋0⦌)} (f : X ⟶ Y) :
    GadgetsOver X a b ⥤ GadgetsOver Y (f.app _ a) (f.app _ b) where
  obj P := ⟨(CostructuredArrow.map f).obj P.obj, by
    constructor
    · change f.app _ (P.obj.hom.app _ P.obj.left.alpha) = f.app _ a
      rw [P.property.1]
    · change f.app _ (P.obj.hom.app _ P.obj.left.omega) = f.app _ b
      rw [P.property.2]⟩
  map h := ObjectProperty.homMk ((CostructuredArrow.map f).map h.hom)
  map_id P := by
    apply ObjectProperty.hom_ext
    exact (CostructuredArrow.map f).map_id P.obj
  map_comp h k := by
    apply ObjectProperty.hom_ext
    exact (CostructuredArrow.map f).map_comp h.hom k.hom

end

end DaggerOriginalProductGadget
