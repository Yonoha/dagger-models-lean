import OriginalActionFreeForgetAdjunction

/-!
# Cofree actions and the native forgetful functor

Mathlib's right adjoint to evaluation gives the cofree action. Its literal
underlying map is the product of the original map over the monoid.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace DaggerOriginalActionForgetCofreeAdjunction

noncomputable section

variable (V : Type v) [Category.{w} V] (G : Type u) [Monoid G]
variable [HasLimitsOfSize.{u, u} V]

/-- The cofree action obtained from the native evaluation right adjoint. -/
def cofreeActionFunctor : V ⥤ Action V G :=
  evaluationRightAdjoint V (SingleObj.star G) ⋙
    (Action.functorCategoryEquivalence V G).inverse

/-- The literal forgetful functor is left adjoint to the cofree action. -/
def forgetCofreeAdjunction : Action.forget V G ⊣ cofreeActionFunctor V G :=
  ((Action.functorCategoryEquivalence V G).toAdjunction.comp
    (evaluationAdjunctionLeft V (SingleObj.star G))).ofNatIsoLeft
      (Action.functorCategoryEquivalenceCompEvaluation V G)

/-- Forgetful lifting is exactly lifting against the cofree image of the map. -/
theorem forget_lifting_iff {X Y : Action V G} (i : X ⟶ Y)
    {A B : V} (p : A ⟶ B) :
    HasLiftingProperty i.hom p ↔
      HasLiftingProperty i ((cofreeActionFunctor V G).map p) :=
  ((forgetCofreeAdjunction V G).hasLiftingProperty_iff i p)

/-- The underlying cofree map is the product of the original map over G. -/
theorem cofreeAction_map_hom {A B : V} (p : A ⟶ B) :
    ((cofreeActionFunctor V G).map p).hom = Limits.Pi.map (fun (_ : G) ↦ p) := rfl

end

end DaggerOriginalActionForgetCofreeAdjunction
