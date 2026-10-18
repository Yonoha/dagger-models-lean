import OriginalActionFreeForgetAdjunction
import Mathlib.CategoryTheory.Types.Basic

/-!
# The native Hom functor of a free action

The free/forgetful adjunction identifies the actual Hom functor from a free
object with the underlying Hom functor after the literal forgetful functor.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite
open DaggerOriginalActionFreeForgetAdjunction

universe u v w

namespace DaggerOriginalActionFreeCoyoneda

noncomputable section

variable (V : Type v) [Category.{w} V] (G : Type u) [Monoid G]
variable [HasColimitsOfSize.{u, u} V]

/-- The actual adjunction Hom equivalences, natural in the target action. -/
def freeCoyonedaIso (A : V) :
    coyoneda.obj (op ((freeActionFunctor V G).obj A)) ≅
      Action.forget V G ⋙ coyoneda.obj (op A) :=
  NatIso.ofComponents (fun X ↦ ((freeForgetAdjunction V G).homEquiv A X).toIso)
    (by
      intro X Y f
      ext k
      exact (freeForgetAdjunction V G).homEquiv_naturality_right k f)

end

end DaggerOriginalActionFreeCoyoneda
