import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
import Mathlib.CategoryTheory.Category.ULift

/-! Only Mathlib is imported; the full chains in both directions are fixed. -/
set_option autoImplicit false
open CategoryTheory
universe u
namespace DaggerNativeSmallHomNerveLiftChallenge
noncomputable section

def statement : Prop := ∀ (C : Type u) [Category.{0} C],
  ∃ e : nerve C ≅ nerve (ULiftHom.{u} C),
    (∀ q (x : (nerve C).obj q),
      e.hom.app q x = (ULiftHom.up.{0, u, u}.mapComposableArrows q.unop.len).obj x) ∧
    (∀ q (x : (nerve (ULiftHom.{u} C)).obj q),
      e.inv.app q x = (ULiftHom.down.{0, u, u}.mapComposableArrows q.unop.len).obj x)

end
end DaggerNativeSmallHomNerveLiftChallenge
