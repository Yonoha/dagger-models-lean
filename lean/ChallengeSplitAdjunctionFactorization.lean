import Mathlib.CategoryTheory.LiftingProperties.Adjunction
import Mathlib.CategoryTheory.MorphismProperty.Factorization
import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty

/-!
Independent specification of canonical factorization through a split left adjoint.
All categories, arrow classes, the full adjunction and the full section iso are explicit.
No factorization in the target category or target model structure is assumed.
-/
set_option autoImplicit false
open CategoryTheory
universe u v a b
namespace DaggerChallengeSplitAdjunctionFactorization

/-- A source canonical factorization descends through the specified split adjunction. -/
def Statement : Prop :=
  ∀ (C : Type u) (_ : Category.{v} C) (D : Type a) (_ : Category.{b} D)
    (L : D ⥤ C) (R S : C ⥤ D) (_ : L ⊣ R) (_ : S ⋙ L ≅ 𝟭 C)
    (P : MorphismProperty C) (Q : MorphismProperty D)
    (_ : P.RespectsIso) (_ : Q.llp.HasFactorization Q),
    Q = P.inverseImage L →
    (∀ {X Y : C} (p : X ⟶ Y), P p → Q (R.map p)) →
      P.llp.HasFactorization P

end DaggerChallengeSplitAdjunctionFactorization
