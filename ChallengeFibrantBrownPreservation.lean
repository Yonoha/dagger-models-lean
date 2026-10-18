import Mathlib.AlgebraicTopology.ModelCategory.BrownLemma

set_option autoImplicit false

open CategoryTheory HomotopicalAlgebra

universe u v u' v'

namespace ChallengeFibrantBrownPreservation

/-- The statement alone: preservation on trivial fibrations implies preservation between fibrants.
-/
def Statement : Prop :=
  ∀ (C : Type u) [Category.{v} C] [ModelCategory C]
    (D : Type u') [Category.{v'} D] [ModelCategory D] (F : C ⥤ D),
    (∀ {X Y : C} (p : X ⟶ Y), Fibration p → WeakEquivalence p → WeakEquivalence (F.map p)) →
    ∀ {X Y : C}, IsFibrant X → IsFibrant Y →
      ∀ (p : X ⟶ Y), WeakEquivalence p → WeakEquivalence (F.map p)

end ChallengeFibrantBrownPreservation
