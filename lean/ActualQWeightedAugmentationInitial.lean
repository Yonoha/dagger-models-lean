import ActualQWeightedAugmentationIsomorphisms

/-! The unchanged augmentation is an isomorphism on every actual initial object. -/
set_option autoImplicit false
open CategoryTheory Limits HomotopicalAlgebra
open DaggerSSetGluing DaggerActualQWeightedResolutionFunctor
open DaggerOriginalCounitRightConeQRealizationAdjunction
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerActualQWeightedAugmentationInitial
noncomputable section

/-- Both original functors preserve the native initial object, so their augmentation is weak. -/
theorem initial_GW (X : SSet.{u}) (hX : IsInitial X) : GW (augmentation.app X) := by
  have : PreservesColimitsOfSize.{0, 0} realization.{u} :=
    preservesColimitsOfSize_shrink.{0, u, 0, u} realization
  have hF : IsInitial (functor.obj X) := initialIsInitial.ofIso
    ((PreservesInitial.iso functor.{u}).symm ≪≫ functor.mapIso (initialIsoIsInitial hX))
  have hG : IsInitial (realization.obj X) := initialIsInitial.ofIso
    ((PreservesInitial.iso realization.{u}).symm ≪≫ realization.mapIso (initialIsoIsInitial hX))
  have : IsIso (augmentation.app X) := isIso_of_isInitial hF hG _
  exact (weakEquivalence_iff_GW _).1 inferInstance

end
end DaggerActualQWeightedAugmentationInitial
