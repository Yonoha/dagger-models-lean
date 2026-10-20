import Mathlib.AlgebraicTopology.ModelCategory.Basic
import Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant

set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra
universe u v
namespace ChallengeCofibrantReplacementComparison

/-- A cofibrant weak approximation lifts by a weak equivalence through any trivial fibration. -/
def Statement : Prop :=
  ∀ (C : Type u) [Category.{v} C] [ModelCategory C] (X Y T : C),
    IsCofibrant X → ∀ (q : X ⟶ T) (p : Y ⟶ T),
      WeakEquivalence q → Fibration p → WeakEquivalence p →
        ∃ l : X ⟶ Y, l ≫ p = q ∧ WeakEquivalence l

end ChallengeCofibrantReplacementComparison
