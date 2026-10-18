import Mathlib.AlgebraicTopology.ModelCategory.BrownLemma

set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra
universe u v u' v'
namespace ChallengeContravariantCofibrantBrown

/-- Contravariant preservation on trivial cofibrations suffices between cofibrant objects. -/
def Statement : Prop :=
  ∀ (C : Type u) [Category.{v} C] [ModelCategory C]
    (D : Type u') [Category.{v'} D] [ModelCategory D] (F : Cᵒᵖ ⥤ D),
    (∀ {X Y : C} (i : X ⟶ Y),
      Cofibration i → WeakEquivalence i → WeakEquivalence (F.map i.op)) →
    ∀ {X Y : C}, IsCofibrant X → IsCofibrant Y →
      ∀ (f : X ⟶ Y), WeakEquivalence f → WeakEquivalence (F.map f.op)

end ChallengeContravariantCofibrantBrown
