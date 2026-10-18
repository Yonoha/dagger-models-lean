import OriginalEquivalenceFactorizationTransport
import Mathlib.AlgebraicTopology.ModelCategory.Basic

/-!
# Native model transport with explicitly identified original arrow classes

Finite limits and colimits are supplied in the target category. Every weak, fibration
and cofibration class is required to be exactly the inverse image of the source class.
The source model gives all closure, both complete factorizations and both lifting laws.
-/
set_option autoImplicit false
open CategoryTheory Limits HomotopicalAlgebra
open DaggerOriginalEquivalenceFactorizationTransport
universe u v a b
namespace DaggerOriginalEquivalenceModelTransport
noncomputable section
variable {C : Type u} [Category.{v} C] {D : Type a} [Category.{b} D]
variable [CategoryWithWeakEquivalences C] [CategoryWithFibrations C]
  [CategoryWithCofibrations C] [HasFiniteLimits C] [HasFiniteColimits C] [ModelCategory D]

/-- Exact source-model transport, with both target factorizations and lifting laws proved. -/
def transportModel (E : C ≌ D)
    (hw : weakEquivalences C = (weakEquivalences D).inverseImage E.functor)
    (hf : fibrations C = (fibrations D).inverseImage E.functor)
    (hc : cofibrations C = (cofibrations D).inverseImage E.functor) : ModelCategory C := by
  haveI : (weakEquivalences C).HasTwoOutOfThreeProperty := by rw [hw]; infer_instance
  haveI : (weakEquivalences C).IsStableUnderRetracts := by rw [hw]; infer_instance
  haveI : (fibrations C).IsStableUnderRetracts := by rw [hf]; infer_instance
  haveI : (cofibrations C).IsStableUnderRetracts := by rw [hc]; infer_instance
  haveI : (trivialCofibrations C).HasFactorization (fibrations C) := by
    change (cofibrations C ⊓ weakEquivalences C).HasFactorization (fibrations C)
    rw [hc, hw, hf]
    change ((trivialCofibrations D).inverseImage E.functor).HasFactorization
      ((fibrations D).inverseImage E.functor)
    exact inverseImageHasFactorization E (trivialCofibrations D) (fibrations D)
  haveI : (cofibrations C).HasFactorization (trivialFibrations C) := by
    change (cofibrations C).HasFactorization (fibrations C ⊓ weakEquivalences C)
    rw [hc, hf, hw]
    change ((cofibrations D).inverseImage E.functor).HasFactorization
      ((trivialFibrations D).inverseImage E.functor)
    exact inverseImageHasFactorization E (cofibrations D) (trivialFibrations D)
  exact
    { cm4a := by
        intro A B X Y i p hi wi fp
        haveI : Cofibration (E.functor.map i) := (cofibration_iff _).2 (by
          simpa only [hc, MorphismProperty.inverseImage_iff] using (cofibration_iff i).1 hi)
        haveI : WeakEquivalence (E.functor.map i) := (weakEquivalence_iff _).2 (by
          simpa only [hw, MorphismProperty.inverseImage_iff] using (weakEquivalence_iff i).1 wi)
        haveI : Fibration (E.functor.map p) := (fibration_iff _).2 (by
          simpa only [hf, MorphismProperty.inverseImage_iff] using (fibration_iff p).1 fp)
        exact reflectsLifting E i p inferInstance
      cm4b := by
        intro A B X Y i p hi fp wp
        haveI : Cofibration (E.functor.map i) := (cofibration_iff _).2 (by
          simpa only [hc, MorphismProperty.inverseImage_iff] using (cofibration_iff i).1 hi)
        haveI : Fibration (E.functor.map p) := (fibration_iff _).2 (by
          simpa only [hf, MorphismProperty.inverseImage_iff] using (fibration_iff p).1 fp)
        haveI : WeakEquivalence (E.functor.map p) := (weakEquivalence_iff _).2 (by
          simpa only [hw, MorphismProperty.inverseImage_iff] using (weakEquivalence_iff p).1 wp)
        exact reflectsLifting E i p inferInstance }

end
end DaggerOriginalEquivalenceModelTransport
