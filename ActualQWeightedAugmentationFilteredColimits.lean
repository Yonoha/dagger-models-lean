import ActualQWeightedAugmentationPushouts

/-! Transfer original augmentation weakness through monomorphic filtered colimits. -/
set_option autoImplicit false
open CategoryTheory Limits HomotopicalAlgebra
open DaggerSSetGluing DaggerActualQWeightedResolutionFunctor
open DaggerOriginalCounitRightConeQRealizationAdjunction
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerActualQWeightedAugmentationFilteredColimits
noncomputable section

/-- Reuse the original geometric filtered-colimit comparison for the unchanged augmentation. -/
theorem filtered_GW {J : Type u} [SmallCategory J] [IsFiltered J]
    (D : J ⥤ SSet.{u}) (c : Cocone D) (hc : IsColimit c)
    (hD : ∀ {a b : J} (f : a ⟶ b), Mono (D.map f))
    (hη : ∀ j, GW (augmentation.app (D.obj j))) : GW (augmentation.app c.pt) := by
  apply DaggerGeometricFilteredColimits.geometric_of_filtered_mono
    (isColimitOfPreserves functor hc) (isColimitOfPreserves realization hc)
    (fun {a b} f ↦ ?_) (fun {a b} f ↦ ?_)
    (D.whiskerLeft augmentation) (augmentation.app c.pt)
    (fun j ↦ augmentation.naturality (c.ι.app j)) hη
  · have : Mono (D.map f) := hD f
    letI : Cofibration (D.map f) := SSet.modelCategoryQuillen.cofibration_of_mono _
    have : Cofibration (functor.map (D.map f)) := inferInstance
    change Mono (functor.map (D.map f))
    exact inferInstance
  · have : Mono (D.map f) := hD f
    letI : Cofibration (D.map f) := SSet.modelCategoryQuillen.cofibration_of_mono _
    have : Cofibration (realization.map (D.map f)) := inferInstance
    change Mono (realization.map (D.map f))
    exact inferInstance

/-- The same original comparison handles the native natural-number skeleton index. -/
theorem sequential_GW (D : ℕ ⥤ SSet.{u}) (c : Cocone D) (hc : IsColimit c)
    (hD : ∀ {a b : ℕ} (f : a ⟶ b), Mono (D.map f))
    (hη : ∀ n, GW (augmentation.app (D.obj n))) : GW (augmentation.app c.pt) := by
  have : PreservesColimitsOfSize.{0, 0} realization.{u} :=
    preservesColimitsOfSize_shrink.{0, u, 0, u} realization
  apply DaggerGeometricFilteredColimits.geometric_of_nat_mono
    (isColimitOfPreserves functor hc) (isColimitOfPreserves realization hc)
    (fun {a b} f ↦ ?_) (fun {a b} f ↦ ?_)
    (D.whiskerLeft augmentation) (augmentation.app c.pt)
    (fun n ↦ augmentation.naturality (c.ι.app n)) hη
  · have : Mono (D.map f) := hD f
    letI : Cofibration (D.map f) := SSet.modelCategoryQuillen.cofibration_of_mono _
    have : Cofibration (functor.map (D.map f)) := inferInstance
    change Mono (functor.map (D.map f))
    exact inferInstance
  · have : Mono (D.map f) := hD f
    letI : Cofibration (D.map f) := SSet.modelCategoryQuillen.cofibration_of_mono _
    have : Cofibration (realization.map (D.map f)) := inferInstance
    change Mono (realization.map (D.map f))
    exact inferInstance

end
end DaggerActualQWeightedAugmentationFilteredColimits
