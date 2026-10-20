import NativeHoCovariantInverseRecognition
import NativeIhomTensorFirstNaturality
import NativeJoyalMappingTensor

/-!
# Restriction along every original weak map is weak into every quasi-category

For every parameter K, the actual ihom(K) map of restriction is conjugate to
the original precomposition test for f tensor K. Two of these exact covariant
tests supply a full inverse, so the original all-target weak predicate follows.
-/
set_option autoImplicit false
open CategoryTheory MonoidalCategory
open DaggerNativeIhomHoObjects DaggerNativeIhomTensorComparison
open DaggerNativeIhomTensorFirstNaturality DaggerNativeJoyalMappingTensor
open DaggerNativeCatEquivalenceWeakProperties DaggerNativeJoyalMappingTest
open DaggerNativeHoCovariantInverseRecognition
universe u
namespace DaggerNativeJoyalWeakRestriction
noncomputable section

theorem restriction_post_equivalence {A B : SSet.{u}} (f : A ⟶ B)
    (hf : weakCategoricalEquivalences f) (Z K : SSet.{u}) [Z.Quasicategory] :
    (postHoFunctor K ((MonoidalClosed.pre f).app Z)).IsEquivalence := by
  let g := (MonoidalClosed.pre (f ▷ K)).app Z
  let h := (ihom K).map ((MonoidalClosed.pre f).app Z)
  let eA := comparisonIso A K Z
  let eB := comparisonIso B K Z
  have hs : eB.inv ≫ g = h ≫ eA.inv := by
    apply (cancel_mono eA.hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [← pre_first_naturality K Z f]
    rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  let e : Arrow.mk (SSet.hoFunctor.map h) ≅ Arrow.mk (SSet.hoFunctor.map g) :=
    Arrow.isoMk (SSet.hoFunctor.mapIso eB.symm) (SSet.hoFunctor.mapIso eA.symm) (by
      change SSet.hoFunctor.map eB.inv ≫ SSet.hoFunctor.map g =
        SSet.hoFunctor.map h ≫ SSet.hoFunctor.map eA.inv
      rw [← SSet.hoFunctor.map_comp, ← SSet.hoFunctor.map_comp]
      exact congrArg SSet.hoFunctor.map hs)
  exact equivalences.of_retract (Retract.ofIso e) ((weak_whiskerRight f hf K) Z)

theorem restriction_weak {A B : SSet.{u}} (f : A ⟶ B)
    (hf : weakCategoricalEquivalences f) (Z : SSet.{u}) [Z.Quasicategory] :
    weakCategoricalEquivalences ((MonoidalClosed.pre f).app Z) :=
  weak_of_post_equivalences _ (restriction_post_equivalence f hf Z _)
    (restriction_post_equivalence f hf Z _)

end
end DaggerNativeJoyalWeakRestriction
