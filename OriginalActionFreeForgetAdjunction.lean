import Mathlib.CategoryTheory.Action.Limits
import Mathlib.CategoryTheory.Adjunction.Evaluation
import Mathlib.CategoryTheory.LiftingProperties.Adjunction

/-!
# Free actions and the native forgetful functor

The free action is obtained from Mathlib's evaluation left adjoint through the
native equivalence with functors on `SingleObj G`. The lifting equivalence uses
Mathlib's adjunction theorem, with no model-category hypotheses.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace DaggerOriginalActionFreeForgetAdjunction

noncomputable section

variable (V : Type v) [Category.{w} V] (G : Type u) [Monoid G]
variable [HasColimitsOfSize.{u, u} V]

/-- The regular free action, using the native left adjoint of evaluation. -/
def freeActionFunctor : V ⥤ Action V G :=
  evaluationLeftAdjoint V (SingleObj.star G) ⋙
    (Action.functorCategoryEquivalence V G).inverse

/-- The free action is left adjoint to the literal underlying-object functor. -/
def freeForgetAdjunction : freeActionFunctor V G ⊣ Action.forget V G :=
  ((evaluationAdjunctionRight V (SingleObj.star G)).comp
    (Action.functorCategoryEquivalence V G).symm.toAdjunction).ofNatIsoRight
      (Action.functorCategoryEquivalenceCompEvaluation V G)

/-- Free-action lifting is exactly lifting of the original underlying map. -/
theorem freeAction_lifting_iff {A B : V} (i : A ⟶ B)
    {X Y : Action V G} (p : X ⟶ Y) :
    HasLiftingProperty ((freeActionFunctor V G).map i) p ↔
      HasLiftingProperty i p.hom :=
  (freeForgetAdjunction V G).hasLiftingProperty_iff i p

end

end DaggerOriginalActionFreeForgetAdjunction
