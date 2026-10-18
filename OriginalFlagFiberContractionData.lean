import OriginalFlagFiberTerminal
import OriginalFlagDiscreteNerve
import Mathlib.CategoryTheory.Functor.Const
import Mathlib.CategoryTheory.Discrete.Basic

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial

universe u

namespace DaggerOriginalFlagFlankification

noncomputable section

open DaggerChosenRigidificationNecklace NecklaceCode

variable (X : SSet.{u}) (a b : X.obj (op ⦋0⦌)) (n : ℕ)
variable (t : (flagHom X a b).obj (op ⦋n⦌))

/-- The same accepted center, forgetting only its flanked proof. -/
abbrev fiberCenterObj : Fiber X a b n t := (fiberCenter X a b n t).obj

/-- The existing first leg, without changing its original arrow. -/
abbrev fiberAlpha := inclusionFiber X a b n t

/-- The terminal arrow is on the same flanked fiber and same normal center. -/
def fiberTerminalNatTrans :
    𝟭 (FlankedFiber X a b n t) ⟶
      (Functor.const (FlankedFiber X a b n t)).obj (fiberCenter X a b n t) where
  app p := (fiberCenterIsTerminal X a b n t).from p
  naturality p q f := by
    change f ≫ (fiberCenterIsTerminal X a b n t).from q =
      (fiberCenterIsTerminal X a b n t).from p ≫ 𝟙 _
    simpa only [Category.comp_id] using (fiberCenterIsTerminal X a b n t).comp_from f

/-- The second original leg is the forgotten arrow to that same terminal center. -/
def fiberToCenter :
    flankToFlankedFiber X a b n t ⋙ forgetFlankedFiber X a b n t ⟶
      (Functor.const (Fiber X a b n t)).obj (fiberCenterObj X a b n t) where
  app p := (forgetFlankedFiber X a b n t).map
    ((fiberCenterIsTerminal X a b n t).from ((flankToFlankedFiber X a b n t).obj p))
  naturality p q f := by
    change (forgetFlankedFiber X a b n t).map ((flankToFlankedFiber X a b n t).map f) ≫
        (forgetFlankedFiber X a b n t).map
          ((fiberCenterIsTerminal X a b n t).from ((flankToFlankedFiber X a b n t).obj q)) =
      (forgetFlankedFiber X a b n t).map
          ((fiberCenterIsTerminal X a b n t).from ((flankToFlankedFiber X a b n t).obj p)) ≫
        𝟙 _
    rw [← Functor.map_comp, (fiberCenterIsTerminal X a b n t).comp_from]
    rw [Category.comp_id]

theorem fiberTerminalNatTrans_app (p : FlankedFiber X a b n t) :
    (fiberTerminalNatTrans X a b n t).app p =
      (fiberCenterIsTerminal X a b n t).from p := rfl

theorem fiberToCenter_app (p : Fiber X a b n t) :
    (fiberToCenter X a b n t).app p = (forgetFlankedFiber X a b n t).map
      ((fiberCenterIsTerminal X a b n t).from ((flankToFlankedFiber X a b n t).obj p)) := rfl

theorem fiberToCenter_original_arrow (p : Fiber X a b n t) :
    ((fiberToCenter X a b n t).app p).hom =
      ((fiberCenterIsTerminal X a b n t).from
        ((flankToFlankedFiber X a b n t).obj p)).hom.hom := rfl

theorem fiberToCenter_triangle (p : Fiber X a b n t) :
    ((fiberToCenter X a b n t).app p).hom.val.hom.map ≫
        (fiberCenterObj X a b n t).obj.1.map =
      ((flankToFlankedFiber X a b n t ⋙ forgetFlankedFiber X a b n t).obj p).obj.1.map :=
  ((fiberToCenter X a b n t).app p).hom.val.w

theorem fiberToCenter_first (p : Fiber X a b n t) :
    ((fiberToCenter X a b n t).app p).hom.val.hom.map.app (op ⦋0⦌)
        ((flankToFlankedFiber X a b n t ⋙ forgetFlankedFiber X a b n t).obj p).obj.1.code.first =
      (fiberCenterObj X a b n t).obj.1.code.first :=
  ((fiberToCenter X a b n t).app p).hom.val.hom.first

theorem fiberToCenter_last (p : Fiber X a b n t) :
    ((fiberToCenter X a b n t).app p).hom.val.hom.map.app (op ⦋0⦌)
        ((flankToFlankedFiber X a b n t ⋙ forgetFlankedFiber X a b n t).obj p).obj.1.code.last =
      (fiberCenterObj X a b n t).obj.1.code.last :=
  ((fiberToCenter X a b n t).app p).hom.val.hom.last

theorem fiberToCenter_flag (p : Fiber X a b n t) :
    NecklaceCode.Flag.map ((fiberToCenter X a b n t).app p).hom.val.hom
        ((flankToFlankedFiber X a b n t ⋙ forgetFlankedFiber X a b n t).obj p).obj.2 =
      (fiberCenterObj X a b n t).obj.2 :=
  ((fiberToCenter X a b n t).app p).hom.property

theorem fiberAlpha_original_arrow (p : Fiber X a b n t) :
    ((fiberAlpha X a b n t).app p).hom = (inclusion X a b n).app p.obj := rfl

theorem fiberAlpha_triangle (p : Fiber X a b n t) :
    ((fiberAlpha X a b n t).app p).hom.val.hom.map ≫ p.obj.1.map =
      ((flankToFlankedFiber X a b n t ⋙ forgetFlankedFiber X a b n t).obj p).obj.1.map :=
  ((fiberAlpha X a b n t).app p).hom.val.w

theorem fiberAlpha_first (p : Fiber X a b n t) :
    ((fiberAlpha X a b n t).app p).hom.val.hom.map.app (op ⦋0⦌)
        ((flankToFlankedFiber X a b n t ⋙ forgetFlankedFiber X a b n t).obj p).obj.1.code.first =
      p.obj.1.code.first := ((fiberAlpha X a b n t).app p).hom.val.hom.first

theorem fiberAlpha_last (p : Fiber X a b n t) :
    ((fiberAlpha X a b n t).app p).hom.val.hom.map.app (op ⦋0⦌)
        ((flankToFlankedFiber X a b n t ⋙ forgetFlankedFiber X a b n t).obj p).obj.1.code.last =
      p.obj.1.code.last := ((fiberAlpha X a b n t).app p).hom.val.hom.last

theorem fiberAlpha_flag (p : Fiber X a b n t) :
    NecklaceCode.Flag.map ((fiberAlpha X a b n t).app p).hom.val.hom
        ((flankToFlankedFiber X a b n t ⋙ forgetFlankedFiber X a b n t).obj p).obj.2 =
      p.obj.2 := ((fiberAlpha X a b n t).app p).hom.property

theorem fiberCenterObj_class : classOf X a b n (fiberCenterObj X a b n t).obj = t :=
  fiberCenter_class X a b n t

/-- The point of the original restricted-fiber contract, in exactly universe u. -/
abbrev fiberPointCat : Type u := Discrete (PUnit.{u+1})

def fiberCollapseFunctor : Fiber X a b n t ⥤ fiberPointCat.{u} :=
  (Functor.const (Fiber X a b n t)).obj (Discrete.mk PUnit.unit)

def fiberCenterFunctor : fiberPointCat.{u} ⥤ Fiber X a b n t :=
  (Functor.const fiberPointCat.{u}).obj (fiberCenterObj X a b n t)

def fiberCollapse : nerve (Fiber X a b n t) ⟶ nerve fiberPointCat.{u} :=
  nerveMap (fiberCollapseFunctor X a b n t)

def fiberSection : nerve fiberPointCat.{u} ⟶ nerve (Fiber X a b n t) :=
  nerveMap (fiberCenterFunctor X a b n t)

def fiberCollapseCenterIso :
    fiberCollapseFunctor X a b n t ⋙ fiberCenterFunctor X a b n t ≅
      (Functor.const (Fiber X a b n t)).obj (fiberCenterObj X a b n t) :=
  Functor.constComp (J := Fiber X a b n t) (Discrete.mk PUnit.unit)
    (fiberCenterFunctor X a b n t)

def fiberCenterCollapseIso :
    fiberCenterFunctor X a b n t ⋙ fiberCollapseFunctor X a b n t ≅
      𝟭 fiberPointCat.{u} :=
  Discrete.natIso (fun _ ↦ eqToIso (Subsingleton.elim _ _))

theorem fiberCollapseCenterIso_hom_app (p : Fiber X a b n t) :
    (fiberCollapseCenterIso X a b n t).hom.app p = 𝟙 (fiberCenterObj X a b n t) := rfl

theorem fiberCollapseCenterIso_inv_app (p : Fiber X a b n t) :
    (fiberCollapseCenterIso X a b n t).inv.app p = 𝟙 (fiberCenterObj X a b n t) := rfl

theorem fiberCenterCollapseIso_hom_app (p : fiberPointCat.{u}) :
    (fiberCenterCollapseIso X a b n t).hom.app p = eqToHom (Subsingleton.elim _ _) := rfl

theorem fiberCenterCollapseIso_inv_app (p : fiberPointCat.{u}) :
    (fiberCenterCollapseIso X a b n t).inv.app p = eqToHom (Subsingleton.elim _ _) := rfl

theorem fiberCollapse_app (k : SimplexCategoryᵒᵖ)
    (gamma : (nerve (Fiber X a b n t)).obj k) :
    (fiberCollapse X a b n t).app k gamma =
      discreteConstantChain (PUnit.{u+1}) k PUnit.unit := by
  apply CategoryTheory.Functor.hext
  · intro i
    rfl
  · intro i j f
    rfl

theorem fiberSection_app (k : SimplexCategoryᵒᵖ)
    (gamma : (nerve fiberPointCat.{u}).obj k) :
    (fiberSection X a b n t).app k gamma =
      (Functor.const (Fin (k.unop.len + 1))).obj (fiberCenterObj X a b n t) := by
  apply CategoryTheory.Functor.hext
  · intro i
    rfl
  · intro i j f
    rfl

theorem fiberCollapse_operator {k l : SimplexCategoryᵒᵖ} (e : k ⟶ l)
    (gamma : (nerve (Fiber X a b n t)).obj k) :
    (nerve fiberPointCat.{u}).map e ((fiberCollapse X a b n t).app k gamma) =
      (fiberCollapse X a b n t).app l ((nerve (Fiber X a b n t)).map e gamma) :=
  (congrFun ((fiberCollapse X a b n t).naturality e) gamma).symm

theorem fiberSection_operator {k l : SimplexCategoryᵒᵖ} (e : k ⟶ l)
    (gamma : (nerve fiberPointCat.{u}).obj k) :
    (nerve (Fiber X a b n t)).map e ((fiberSection X a b n t).app k gamma) =
      (fiberSection X a b n t).app l ((nerve fiberPointCat.{u}).map e gamma) :=
  (congrFun ((fiberSection X a b n t).naturality e) gamma).symm

end

end DaggerOriginalFlagFlankification
