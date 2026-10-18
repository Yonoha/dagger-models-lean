import ActualQWeightedAugmentationCoproducts
import ActualQWeightedAugmentationFilteredColimits

/-! Transport the exact original weighted augmentation through isomorphisms. -/
set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra
open DaggerSSetGluing DaggerActualQWeightedResolutionFunctor
open DaggerOriginalCounitRightConeQRealizationAdjunction
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerActualQWeightedAugmentationIsomorphisms
noncomputable section

/-- Naturality transports augmentation weakness across an actual simplicial isomorphism. -/
theorem iso_GW {X Y : SSet.{u}} (e : X ≅ Y)
    (hX : GW (augmentation.app X)) : GW (augmentation.app Y) := by
  have : WeakEquivalence (augmentation.app X) := (weakEquivalence_iff_GW _).2 hX
  have : WeakEquivalence (functor.map e.hom) := inferInstance
  have : WeakEquivalence (realization.map e.hom) := inferInstance
  exact (weakEquivalence_iff_GW _).1
    (weakEquivalence_of_precomp_of_fac (augmentation.naturality e.hom))

end
end DaggerActualQWeightedAugmentationIsomorphisms
