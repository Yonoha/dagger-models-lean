import OriginalFlagFiberZigzags
import OriginalFlagFlankedDescent
import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal

/-!
Terminal objects in the original flanked augmentation fibers.

This source draft uses the existing connected-object induction and the actual
descent arrow. Its imports and proof bodies have not yet been checked by Lean.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial

universe u

namespace DaggerOriginalFlagFlankification

noncomputable section

open DaggerChosenRigidificationNecklace NecklaceCode

variable (X : SSet.{u}) (a b : X.obj (op ⦋0⦌)) (n : ℕ)
variable (t : (flagHom X a b).obj (op ⦋n⦌))

/-- Forget only the fiber proof, retaining the same degree object and flag. -/
def flankedFiberDegreeObj (p : FlankedFiber X a b n t) : FlankedDegree X a b n :=
  ⟨p.obj.obj, p.property⟩

/-- Restrict the same descended arrow to the supplied original fiber. -/
def flankedFiberDescent (p q r : FlankedFiber X a b n t)
    (hq : TotallyNondegenerate X a b n q.obj.obj) (f : p ⟶ q) (g : p ⟶ r) : r ⟶ q :=
  ObjectProperty.homMk (ObjectProperty.homMk
    (flankedDegreeDescent (flankedFiberDegreeObj X a b n t p)
      (flankedFiberDegreeObj X a b n t q) (flankedFiberDegreeObj X a b n t r) hq
      (ObjectProperty.homMk f.hom.hom) (ObjectProperty.homMk g.hom.hom)).hom)

/-- Uniqueness retains the whole original arrow, including its flag equation. -/
theorem flankedFiber_hom_unique (p q : FlankedFiber X a b n t)
    (hq : TotallyNondegenerate X a b n q.obj.obj) (f g : p ⟶ q) : f = g := by
  apply ObjectProperty.hom_ext
  apply ObjectProperty.hom_ext
  have h := flankedDegree_hom_unique (flankedFiberDegreeObj X a b n t p)
    (flankedFiberDegreeObj X a b n t q) hq
    (ObjectProperty.homMk f.hom.hom) (ObjectProperty.homMk g.hom.hom)
  exact congrArg (fun k ↦ k.hom) h

/-- Connectedness transports existence to the same supplied nondegenerate target. -/
theorem flankedFiber_hom_nonempty (p q : FlankedFiber X a b n t)
    (hq : TotallyNondegenerate X a b n q.obj.obj) : Nonempty (p ⟶ q) := by
  apply induct_on_objects (J := FlankedFiber X a b n t)
    (fun r ↦ Nonempty (r ⟶ q)) (j₀ := q) (show Nonempty (q ⟶ q) from ⟨𝟙 q⟩)
  intro r s k
  constructor
  · rintro ⟨f⟩
    exact ⟨flankedFiberDescent X a b n t r q s hq f k⟩
  · rintro ⟨f⟩
    exact ⟨k ≫ f⟩

/-- Every supplied totally nondegenerate object is terminal in its actual fiber. -/
def flankedFiberIsTerminal (q : FlankedFiber X a b n t)
    (hq : TotallyNondegenerate X a b n q.obj.obj) : IsTerminal q :=
  IsTerminal.ofUniqueHom
    (fun p ↦ Classical.choice (flankedFiber_hom_nonempty X a b n t p q hq))
    (fun p f ↦ flankedFiber_hom_unique X a b n t p q hq f _)

/-- The center is the normalization of the flank of a representative of this same t. -/
def fiberCenter : FlankedFiber X a b n t :=
  normalizedFlankedFiberObj X a b n t
    ((flankToFlankedFiber X a b n t).obj (Classical.choice (fiber_nonempty X a b n t)))

theorem fiberCenter_nondegenerate :
    TotallyNondegenerate X a b n (fiberCenter X a b n t).obj.obj :=
  normalizedFlankedFiberObj_nondegenerate X a b n t _

theorem fiberCenter_class : classOf X a b n (fiberCenter X a b n t).obj.obj = t :=
  (fiberCenter X a b n t).obj.property

/-- No global nonemptiness or Kan hypothesis is added to the supplied quotient value. -/
def fiberCenterIsTerminal : IsTerminal (fiberCenter X a b n t) :=
  flankedFiberIsTerminal X a b n t (fiberCenter X a b n t)
    (fiberCenter_nondegenerate X a b n t)

end

end DaggerOriginalFlagFlankification
