import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
import Mathlib.CategoryTheory.Discrete.Basic
import Mathlib.CategoryTheory.Functor.Const

set_option autoImplicit false

open CategoryTheory Opposite Simplicial

universe u

namespace DaggerOriginalFlagFlankification

/-- The literal constant simplicial set at Q, with identity operators. -/
abbrev constantSSet (Q : Type u) : SSet.{u} :=
  (Functor.const SimplexCategoryᵒᵖ).obj Q

/-- The literal constant finite chain at the supplied discrete object. -/
def discreteConstantChain (Q : Type u) (k : SimplexCategoryᵒᵖ) (t : Q) :
    (nerve (Discrete Q)).obj k :=
  (Functor.const (Fin (k.unop.len + 1))).obj (Discrete.mk t)

/-- A chain arrow 0→i equates the two actual discrete values. -/
theorem discreteChain_as_eq_zero (Q : Type u) (k : SimplexCategoryᵒᵖ)
    (gamma : (nerve (Discrete Q)).obj k) (i : Fin (k.unop.len + 1)) :
    (gamma.obj i).as = (gamma.obj 0).as :=
  (Discrete.eq_of_hom (gamma.map
    (homOfLE (show (0 : Fin (k.unop.len + 1)) ≤ i from Nat.zero_le i.val)))).symm

/-- Evaluation at the first object; naturality does not require alpha(0)=0. -/
def nerveDiscreteToConstant (Q : Type u) : nerve (Discrete Q) ⟶ constantSSet Q where
  app _ gamma := (gamma.obj 0).as
  naturality {k l} alpha := by
    funext gamma
    change
      (gamma.obj (alpha.unop.toOrderHom 0)).as =
        (gamma.obj 0).as
    exact discreteChain_as_eq_zero Q k gamma _

/-- The inverse sends the supplied value to the full constant chain. -/
def constantToDiscreteNerve (Q : Type u) : constantSSet Q ⟶ nerve (Discrete Q) where
  app k t := discreteConstantChain Q k t
  naturality {k l} alpha := by
    funext t
    apply nerve.ext_of_isThin
    funext i
    rfl

/-- Both whole simplicial inverse laws, including the empty type and universe0. -/
def nerveDiscreteIso (Q : Type u) : nerve (Discrete Q) ≅ constantSSet Q where
  hom := nerveDiscreteToConstant Q
  inv := constantToDiscreteNerve Q
  hom_inv_id := by
    apply NatTrans.ext
    funext k gamma
    apply nerve.ext_of_isThin
    funext i
    apply Discrete.ext
    exact Discrete.eq_of_hom (gamma.map
      (homOfLE (show (0 : Fin (k.unop.len + 1)) ≤ i from Nat.zero_le i.val)))
  inv_hom_id := by
    apply NatTrans.ext
    funext k t
    rfl

theorem nerveDiscreteIso_hom_app (Q : Type u) (k : SimplexCategoryᵒᵖ)
    (gamma : (nerve (Discrete Q)).obj k) :
    (nerveDiscreteIso Q).hom.app k gamma = (gamma.obj 0).as := rfl

theorem nerveDiscreteIso_inv_app (Q : Type u) (k : SimplexCategoryᵒᵖ) (t : Q) :
    (nerveDiscreteIso Q).inv.app k t = discreteConstantChain Q k t := rfl

theorem nerveDiscreteIso_hom_inv (Q : Type u) :
    (nerveDiscreteIso Q).hom ≫ (nerveDiscreteIso Q).inv = 𝟙 (nerve (Discrete Q)) :=
  (nerveDiscreteIso Q).hom_inv_id

theorem nerveDiscreteIso_inv_hom (Q : Type u) :
    (nerveDiscreteIso Q).inv ≫ (nerveDiscreteIso Q).hom = 𝟙 (constantSSet Q) :=
  (nerveDiscreteIso Q).inv_hom_id

/-- This formula retains the actual alpha(0), which can differ from zero. -/
theorem nerveDiscreteIso_hom_operator (Q : Type u) {k l : SimplexCategoryᵒᵖ}
    (alpha : k ⟶ l) (gamma : (nerve (Discrete Q)).obj k) :
    (nerveDiscreteIso Q).hom.app l ((nerve (Discrete Q)).map alpha gamma) =
      (gamma.obj (alpha.unop.toOrderHom 0)).as := rfl

theorem nerveDiscreteIso_hom_naturality (Q : Type u) {k l : SimplexCategoryᵒᵖ}
    (alpha : k ⟶ l) (gamma : (nerve (Discrete Q)).obj k) :
    (nerveDiscreteIso Q).hom.app l ((nerve (Discrete Q)).map alpha gamma) =
      (nerveDiscreteIso Q).hom.app k gamma :=
  discreteChain_as_eq_zero Q k gamma (alpha.unop.toOrderHom 0)

theorem nerveDiscreteIso_inv_naturality (Q : Type u) {k l : SimplexCategoryᵒᵖ}
    (alpha : k ⟶ l) (t : Q) :
    (nerve (Discrete Q)).map alpha ((nerveDiscreteIso Q).inv.app k t) =
      (nerveDiscreteIso Q).inv.app l t := by
  apply nerve.ext_of_isThin
  funext i
  rfl

end DaggerOriginalFlagFlankification
