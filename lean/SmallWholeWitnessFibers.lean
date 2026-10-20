import SimplexInverseWitnessCategory
import Mathlib.CategoryTheory.ObjectProperty.Small

/-!
# A genuinely small family of every complete witness over a small base-arrow family

Every possible whole inverse map and all chosen cells are included. No bound on
those maps is inferred from finite simplex parameters. Only the supplied base
family is restricted; coverage of arbitrary large witnesses is not asserted.
-/
set_option autoImplicit false
open CategoryTheory
open DaggerSimplexInverseWitnessCategory DaggerNativeJoyalWeakSimplexInverse
universe u v w
namespace DaggerSmallWholeWitnessFibers
variable {C : Type w} [Category.{v} C] (R : C ⥤ SSet.{u})
    {K : Type u} (G : K → Arrow C)

abbrev Index := Σ k : K, SimplexInverseData (R.map (G k).hom)

def family (i : Index R G) : Witness R := ⟨G i.1, i.2⟩

theorem underlying_eq (i : Index R G) : (family R G i).arrow = G i.1 := rfl

theorem covers_exact (X : Witness R) :
    (∃ k, G k = X.arrow) ↔ ∃ i : Index R G, family R G i = X := by
  constructor
  · cases X with
    | mk a d =>
      rintro ⟨k, hk⟩
      cases hk
      exact ⟨⟨k, d⟩, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i.1, rfl⟩

instance indexSmall : Small.{u} (Index R G) := inferInstance

instance familySmall : ObjectProperty.Small.{u} (ObjectProperty.ofObj (family R G)) :=
  inferInstance

end DaggerSmallWholeWitnessFibers
