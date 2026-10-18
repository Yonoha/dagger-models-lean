import ActualQWeightedAugmentationPushouts

/-! Extend the exact original augmentation to arbitrary coproducts. -/
set_option autoImplicit false
open CategoryTheory Limits HomotopicalAlgebra
open DaggerSSetGluing DaggerActualQWeightedResolutionFunctor
open DaggerOriginalCounitRightConeQRealizationAdjunction
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerActualQWeightedAugmentationCoproducts
noncomputable section

/-- The two native coproduct comparison maps commute with the original augmentation. -/
theorem coproduct_square {J : Type u} (X : J → SSet.{u}) :
    sigmaComparison functor X ≫ augmentation.app (∐ X) =
      Limits.Sigma.map (fun j ↦ augmentation.app (X j)) ≫ sigmaComparison realization X := by
  apply Limits.Sigma.hom_ext
  intro j
  simp only [ι_comp_sigmaComparison_assoc, Limits.Sigma.ι_map_assoc,
    ι_comp_sigmaComparison]
  exact augmentation.naturality (Limits.Sigma.ι X j)

/-- Weakness of every original component implies weakness on the actual full coproduct. -/
theorem coproduct_GW {J : Type u} (X : J → SSet.{u})
    (hX : ∀ j, GW (augmentation.app (X j))) : GW (augmentation.app (∐ X)) := by
  have : WeakEquivalence (Limits.Sigma.map (fun j ↦ augmentation.app (X j))) :=
    (weakEquivalence_iff_GW _).2
      (DaggerOriginalFlagFlankification.sigmaMap_GW _ hX)
  have : WeakEquivalence (sigmaComparison functor X) := inferInstance
  have : WeakEquivalence (sigmaComparison realization X) := inferInstance
  exact (weakEquivalence_iff_GW _).1
    (weakEquivalence_of_precomp_of_fac (coproduct_square X))

end
end DaggerActualQWeightedAugmentationCoproducts
