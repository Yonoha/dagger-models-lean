import Mathlib.AlgebraicTopology.SimplicialSet.HoFunctorMonoidal
import Mathlib.AlgebraicTopology.Quasicategory.Basic

/-!
# The ordinary weak categorical equivalence mapping test

This is Joyal's mapping-category definition: for every quasicategory Z, native
ho of precomposition Fun(B,Z) -> Fun(A,Z) is an equivalence of ordinary categories.
The agreement with another weak class and a full model structure are separate
mathematical assertions, not fields smuggled into this definition.
Primary reference: Lurie, Higher Topos Theory, the comparison with Joyal's definition.
-/
set_option autoImplicit false
open CategoryTheory
universe u
namespace DaggerNativeJoyalMappingTest

/-- Fix the exact ordinary mapping-category definition on Mathlib's original SSet. -/
def weakCategoricalEquivalences : MorphismProperty SSet.{u} :=
  fun _ _ f ↦ ∀ (Z : SSet.{u}) [SSet.Quasicategory Z],
    (SSet.hoFunctor.map ((MonoidalClosed.pre f).app Z)).toFunctor.IsEquivalence

end DaggerNativeJoyalMappingTest
