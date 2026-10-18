import OriginalFlagFlankedRecoding
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.NatIso

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial

universe u

namespace DaggerOriginalFlagFlankification

noncomputable section

open DaggerChosenRigidificationNecklace NecklaceCode

variable (X : SSet.{u}) (a b : X.obj (op ⦋0⦌)) (n : ℕ)

def flankedPredicate : ObjectProperty (Degree X a b n) := fun p ↦ Flanked p.2

abbrev FlankedDegree := (flankedPredicate X a b n).FullSubcategory

def toFlankedDegree : Degree X a b n ⥤ FlankedDegree X a b n :=
  (flankedPredicate X a b n).lift (flankification X a b n)
    (flankification_flanked)

def forgetFlankedDegree : FlankedDegree X a b n ⥤ Degree X a b n :=
  (flankedPredicate X a b n).ι

/-- Recoding is natural on all original arrows, not just chosen component paths. -/
def recodingDegreeNatIso :
    forgetFlankedDegree X a b n ⋙ toFlankedDegree X a b n ≅ 𝟭 (FlankedDegree X a b n) :=
  NatIso.ofComponents
    (fun p ↦ (flankedPredicate X a b n).isoMk (recodingIso p.obj p.property)) (by
      intro p q f
      apply ObjectProperty.hom_ext
      exact (inclusion X a b n).naturality f.hom)

variable (t : (flagHom X a b).obj (op ⦋n⦌))

def flankFiber : Fiber X a b n t ⥤ Fiber X a b n t :=
  (fiberPredicate X a b n t).lift
    ((fiberPredicate X a b n t).ι ⋙ flankification X a b n) (by
      intro p
      exact (flankification_class p.obj).trans p.property)

def fiberInclusion : flankFiber X a b n t ⟶ 𝟭 (Fiber X a b n t) where
  app p := ObjectProperty.homMk ((inclusion X a b n).app p.obj)
  naturality p q f := by
    apply ObjectProperty.hom_ext
    exact (inclusion X a b n).naturality f.hom

def flankedFiberPredicate : ObjectProperty (Fiber X a b n t) := fun p ↦ Flanked p.obj.2

abbrev FlankedFiber := (flankedFiberPredicate X a b n t).FullSubcategory

def forgetFlankedFiber : FlankedFiber X a b n t ⥤ Fiber X a b n t :=
  (flankedFiberPredicate X a b n t).ι

def flankToFlankedFiber : Fiber X a b n t ⥤ FlankedFiber X a b n t :=
  (flankedFiberPredicate X a b n t).lift (flankFiber X a b n t) (by
    intro p
    exact flankification_flanked p.obj)

theorem flankToFlankedFiber_obj (p : Fiber X a b n t) :
    ((flankToFlankedFiber X a b n t).obj p).obj.obj =
      (flankification X a b n).obj p.obj := rfl

theorem flankToFlankedFiber_map {p q : Fiber X a b n t} (f : p ⟶ q) :
    ((flankToFlankedFiber X a b n t).map f).hom.hom =
      (flankification X a b n).map f.hom := rfl

theorem flankToFlankedFiber_forget :
    flankToFlankedFiber X a b n t ⋙ forgetFlankedFiber X a b n t =
      flankFiber X a b n t := rfl

def inclusionFiber :
    flankToFlankedFiber X a b n t ⋙ forgetFlankedFiber X a b n t ⟶
      𝟭 (Fiber X a b n t) := fiberInclusion X a b n t

def recodingFiberIso (p : FlankedFiber X a b n t) :
    (forgetFlankedFiber X a b n t ⋙ flankToFlankedFiber X a b n t).obj p ≅ p :=
  (flankedFiberPredicate X a b n t).isoMk
    ((fiberPredicate X a b n t).isoMk (recodingIso p.obj.obj p.property))

def recodingFiberNatIso :
    forgetFlankedFiber X a b n t ⋙ flankToFlankedFiber X a b n t ≅
      𝟭 (FlankedFiber X a b n t) :=
  NatIso.ofComponents (recodingFiberIso X a b n t) (by
    intro p q f
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    exact (inclusion X a b n).naturality f.hom.hom)

theorem recodingFiberIso_hom (p : FlankedFiber X a b n t) :
    (recodingFiberIso X a b n t p).hom.hom.hom =
      (inclusion X a b n).app p.obj.obj := rfl

theorem recodingFiberIso_inv_whole (p : FlankedFiber X a b n t) :
    (recodingFiberIso X a b n t p).inv.hom.hom.val.hom.map =
      (recodingInverse p.obj.obj.2 p.property).map := rfl

theorem recodingFiberIso_hom_inv (p : FlankedFiber X a b n t) :
    (recodingFiberIso X a b n t p).hom ≫ (recodingFiberIso X a b n t p).inv = 𝟙 _ :=
  (recodingFiberIso X a b n t p).hom_inv_id

theorem recodingFiberIso_inv_hom (p : FlankedFiber X a b n t) :
    (recodingFiberIso X a b n t p).inv ≫ (recodingFiberIso X a b n t p).hom = 𝟙 _ :=
  (recodingFiberIso X a b n t p).inv_hom_id

end

end DaggerOriginalFlagFlankification
