import ChosenFlagHomColimit
import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.ConnectedComponents

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial

universe u

namespace DaggerOriginalFlagFlankification

noncomputable section

open DaggerChosenRigidificationNecklace NecklaceCode

variable (X : SSet.{u}) (a b : X.obj (op ⦋0⦌)) (n : ℕ)

/-- The existing Elements category, with the original degree diagram and all its arrows. -/
abbrev Degree := (flagDegreeDiagram X a b (op ⦋n⦌)).Elements

/-- The representative is the SAME original FlagHom quotient representative. -/
def classOf (p : Degree X a b n) : (flagHom X a b).obj (op ⦋n⦌) :=
  Quot.mk (flagRelation X a b (op ⦋n⦌)) p

theorem classOf_map {p q : Degree X a b n} (f : p ⟶ q) :
    classOf X a b n p = classOf X a b n q :=
  Quot.sound ⟨f.val, f.property.symm⟩

def augmentation : Degree X a b n ⥤ Discrete ((flagHom X a b).obj (op ⦋n⦌)) where
  obj p := Discrete.mk (classOf X a b n p)
  map f := Discrete.eqToHom (classOf_map X a b n f)

def fiberPredicate (t : (flagHom X a b).obj (op ⦋n⦌)) :
    ObjectProperty (Degree X a b n) := fun p ↦ classOf X a b n p = t

abbrev Fiber (t : (flagHom X a b).obj (op ⦋n⦌)) :=
  (fiberPredicate X a b n t).FullSubcategory

/-- Only a supplied quotient value is used; empty global object sets cause no premise. -/
theorem fiber_nonempty (t : (flagHom X a b).obj (op ⦋n⦌)) :
    Nonempty (Fiber X a b n t) := by
  induction t using Quot.ind with
  | _ p => exact ⟨⟨p, rfl⟩⟩

/-- Both quotient descriptions retain the literal representative, without a semantic kernel. -/
def componentEquiv : ConnectedComponents (Degree X a b n) ≃
    (flagHom X a b).obj (op ⦋n⦌) where
  toFun := ConnectedComponents.liftFunctor _ (augmentation X a b n)
  invFun := Quot.lift (fun p ↦ ConnectedComponents.mk (J := Degree X a b n) p) (by
    rintro p q ⟨f, hf⟩
    exact Quotient.sound (Zigzag.of_hom
      (CategoryOfElements.homMk (F := flagDegreeDiagram X a b (op ⦋n⦌)) p q f hf.symm)))
  left_inv c := by
    induction c using Quotient.inductionOn' with
    | _ p => rfl
  right_inv t := by
    induction t using Quot.ind with
    | _ p => rfl

theorem componentEquiv_mk (p : Degree X a b n) :
    componentEquiv X a b n (ConnectedComponents.mk p) = classOf X a b n p := rfl

theorem componentEquiv_symm_mk (p : Degree X a b n) :
    (componentEquiv X a b n).symm (classOf X a b n p) =
      ConnectedComponents.mk p := rfl

end

end DaggerOriginalFlagFlankification
