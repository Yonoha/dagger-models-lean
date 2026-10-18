import Mathlib.CategoryTheory.LiftingProperties.Adjunction
import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty

set_option autoImplicit false
open CategoryTheory
universe u v u' v'
namespace ChallengeAdjunctionLiftingTransfer

/-- A right adjoint preserving a test class makes its left adjoint preserve the exact LLP. -/
def Statement : Prop :=
  ∀ (C : Type u) [Category.{v} C] (D : Type u') [Category.{v'} D]
    (F : C ⥤ D) (G : D ⥤ C) (_adj : F ⊣ G)
    (P : MorphismProperty D) (Q : MorphismProperty C),
    (∀ {X Y : D} (p : X ⟶ Y), P p → Q (G.map p)) →
    ∀ {A B : C} (i : A ⟶ B), Q.llp i → P.llp (F.map i)

end ChallengeAdjunctionLiftingTransfer
