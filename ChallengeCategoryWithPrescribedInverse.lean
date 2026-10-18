import Mathlib.CategoryTheory.Groupoid.Basic

set_option autoImplicit false
open CategoryTheory
universe u v
namespace ChallengeCategoryWithPrescribedInverse

/-- Both inverse laws give a groupoid preserving the entire category and the prescribed inverse. -/
def Statement : Prop :=
  ∀ (C : Type u) [cat : Category.{v} C]
    (inverse : ∀ {x y : C}, (x ⟶ y) → (y ⟶ x)),
    (∀ {x y : C} (a : x ⟶ y), inverse a ≫ a = 𝟙 y) →
    (∀ {x y : C} (a : x ⟶ y), a ≫ inverse a = 𝟙 x) →
    ∃ G : Groupoid.{v, u} C,
      G.toCategory = cat ∧ HEq (@Groupoid.inv C G) (@inverse)

end ChallengeCategoryWithPrescribedInverse
