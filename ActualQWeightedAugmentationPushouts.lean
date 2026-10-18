import ActualQWeightedResolutionLeftAdjoint

/-! Extend the unchanged weighted augmentation through actual simplicial pushouts. -/
set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra
open DaggerSSetGluing DaggerActualQWeightedResolutionFunctor
open DaggerOriginalCounitRightConeQRealizationAdjunction
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerActualQWeightedAugmentationPushouts
noncomputable section

/-- The original augmentation is weak at a pushout when it is weak at its three inputs. -/
theorem pushout_GW {A X Z P : SSet.{u}} (k : A ⟶ X) (ell : A ⟶ Z)
    (r : X ⟶ P) (s : Z ⟶ P) (sq : IsPushout k ell r s) [Mono k]
    (hA : GW (augmentation.app A)) (hX : GW (augmentation.app X))
    (hZ : GW (augmentation.app Z)) : GW (augmentation.app P) := by
  letI : Cofibration k := SSet.modelCategoryQuillen.cofibration_of_mono k
  have : Cofibration (functor.map k) := inferInstance
  have : Cofibration (realization.map k) := inferInstance
  have : Mono (functor.map k) := inferInstance
  have : Mono (realization.map k) := inferInstance
  exact geometric_of_pushout_cube
    (functor.map k) (functor.map ell) (functor.map r) (functor.map s)
    (realization.map k) (realization.map ell) (realization.map r) (realization.map s)
    (sq.map functor) (sq.map realization)
    (augmentation.app A) (augmentation.app X) (augmentation.app Z) (augmentation.app P)
    (augmentation.naturality k) (augmentation.naturality ell)
    (augmentation.naturality r) (augmentation.naturality s) hA hX hZ

end
end DaggerActualQWeightedAugmentationPushouts
