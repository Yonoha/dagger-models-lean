import ChallengeCategoryWithPrescribedInverse

set_option autoImplicit false
open CategoryTheory
universe u v
namespace DaggerOriginalCategoryWithPrescribedInverseChallengeProof

/-- The native constructor retains the actual category and inverse without changing either. -/
def makeGroupoid (C : Type u) [Category.{v} C]
    (inverse : ∀ {x y : C}, (x ⟶ y) → (y ⟶ x))
    (left : ∀ {x y : C} (a : x ⟶ y), inverse a ≫ a = 𝟙 y)
    (right : ∀ {x y : C} (a : x ⟶ y), a ≫ inverse a = 𝟙 x) : Groupoid.{v, u} C where
  inv := inverse
  inv_comp := left
  comp_inv := right

/-- The native construction satisfies the exact independent preservation statement. -/
theorem challengeProof : ChallengeCategoryWithPrescribedInverse.Statement.{u, v} := by
  intro C cat inverse left right
  exact ⟨makeGroupoid C inverse left right, rfl, HEq.rfl⟩

end DaggerOriginalCategoryWithPrescribedInverseChallengeProof
