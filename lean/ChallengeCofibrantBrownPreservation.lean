import Mathlib.AlgebraicTopology.ModelCategory.BrownLemma

set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra
universe u v u' v'
namespace ChallengeCofibrantBrownPreservation

/-- The independent statement: trivial-cofibration preservation suffices between cofibrants. -/
def Statement : Prop :=
  ∀ (C : Type u) [Category.{v} C] [ModelCategory C]
    (D : Type u') [Category.{v'} D] [ModelCategory D] (F : C ⥤ D),
    (∀ {X Y : C} (i : X ⟶ Y), Cofibration i → WeakEquivalence i → WeakEquivalence (F.map i)) →
    ∀ {X Y : C}, IsCofibrant X → IsCofibrant Y →
      ∀ (f : X ⟶ Y), WeakEquivalence f → WeakEquivalence (F.map f)

end ChallengeCofibrantBrownPreservation
