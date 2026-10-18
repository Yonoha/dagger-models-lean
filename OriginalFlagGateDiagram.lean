import OriginalProductGateSupport
import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial
open DaggerChosenRigidificationNecklace

universe u

namespace DaggerOriginalProductGadget

noncomputable section

variable {X : SSet.{u}}

/-- Actual finite nonempty chains of allowed vertices, ordered by reverse inclusion. -/
def FlagGateIndex (A : Set (X.obj (op ⦋0⦌))) (R : X.obj (op ⦋0⦌) → X.obj (op ⦋0⦌) → Prop) :=
  OrderDual {S : Set (X.obj (op ⦋0⦌)) // S ⊆ A ∧ S.Finite ∧ S.Nonempty ∧ IsChain R S}

instance flagGateIndexPartialOrder (A : Set (X.obj (op ⦋0⦌)))
    (R : X.obj (op ⦋0⦌) → X.obj (op ⦋0⦌) → Prop) : PartialOrder (FlagGateIndex A R) :=
  inferInstanceAs (PartialOrder (OrderDual {S : Set (X.obj (op ⦋0⦌)) //
    S ⊆ A ∧ S.Finite ∧ S.Nonempty ∧ IsChain R S}))

variable (a b : X.obj (op ⦋0⦌)) (A : Set (X.obj (op ⦋0⦌)))
  (R : X.obj (op ⦋0⦌) → X.obj (op ⦋0⦌) → Prop)

/-- The actual subcomplex diagram, with the original Hom as its common ambient simplicial set. -/
def flagGateDiagram : FlagGateIndex A R ⥤ SSet.{u} where
  obj S := (flagGateSubcomplex a b S.val).toFunctor
  map f := Subfunctor.homOfLe (flagGateSubcomplex_antitone a b (leOfHom f))

def flagGateCocone : Cocone (flagGateDiagram a b A R) where
  pt := flagHom X a b
  ι := { app S := (flagGateSubcomplex a b S.val).ι }

/-- A row of the same subcomplex diagram, evaluated at the specified original simplex degree. -/
def flagGateDegreeDiagram (q : SimplexCategoryᵒᵖ) : FlagGateIndex A R ⥤ Type u :=
  flagGateDiagram a b A R ⋙ (evaluation _ _).obj q

def flagGateRowAugmentation (q : SimplexCategoryᵒᵖ) :
    (flagGateDegreeDiagram a b A R q).Elements ⥤ Discrete ((flagHom X a b).obj q) where
  obj p := Discrete.mk p.2.val
  map f := eqToHom (congrArg Discrete.mk (congrArg Subtype.val f.property))

variable {a b} {A R} {q : SimplexCategoryᵒᵖ}

/-- The full fiber of the actual row augmentation over the supplied original flag class. -/
def FlagGateRowFiber (x : (flagHom X a b).obj q) :=
  (show ObjectProperty (flagGateDegreeDiagram a b A R q).Elements from
    fun p ↦ (flagGateRowAugmentation a b A R q).obj p = Discrete.mk x).FullSubcategory

instance flagGateRowFiberCategory (x : (flagHom X a b).obj q) :
    Category (FlagGateRowFiber (A := A) (R := R) x) :=
  inferInstanceAs (Category (ObjectProperty.FullSubcategory _))

theorem flagGateRowFiber_value (x : (flagHom X a b).obj q)
    (p : FlagGateRowFiber (A := A) (R := R) x) : p.obj.2.val = x :=
  congrArg Discrete.as p.property

end

end DaggerOriginalProductGadget
