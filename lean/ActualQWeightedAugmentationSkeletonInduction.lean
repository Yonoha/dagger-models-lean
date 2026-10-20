import ActualQWeightedAugmentationInitial
import NativeSimplicialSkeletonStages

/-! Extend the exact original Q-weighted augmentation along the existing full skeleton. -/
set_option autoImplicit false
open CategoryTheory Limits Simplicial
open DaggerSSetGluing DaggerActualQWeightedResolutionFunctor
open DaggerActualQWeightedAugmentationPushouts DaggerActualQWeightedAugmentationCoproducts
open DaggerActualQWeightedAugmentationIsomorphisms DaggerActualQWeightedAugmentationInitial
open DaggerNativeSimplicialSkeletonStages
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerActualQWeightedAugmentationSkeletonInduction
noncomputable section

/-- The native zero stage is the original empty subcomplex, up to its native isomorphism. -/
theorem zero_GW (X : SSet.{u}) : GW (augmentation.app ((stages X).obj 0)) :=
  iso_GW (SSet.relativeCellComplex X).toTransfiniteCompositionOfShape.isoBot.symm
    (initial_GW _ SSet.Subcomplex.isInitialBot)

/-- Attach all original n-cells using the native boundary coproduct pushout. -/
theorem successor_GW (X : SSet.{u}) (n : ℕ)
    (hX : GW (augmentation.app ((stages X).obj n)))
    (hBoundary : GW (augmentation.app (SSet.boundary.{u} n).toSSet)) :
    GW (augmentation.app ((stages X).obj (n + 1))) := by
  let i := (⊥ : X.Subcomplex).ι
  apply pushout_GW (SSet.relativeCellComplexOfMono.m i n)
    (SSet.relativeCellComplexOfMono.t i n) (SSet.relativeCellComplexOfMono.b i n)
    (SSet.relativeCellComplexOfMono.r i n) (SSet.relativeCellComplexOfMono.isPushout i n).flip
  · exact coproduct_GW
      (fun _ : SSet.relativeCellComplexOfMono.ι i n ↦ (SSet.boundary.{u} n).toSSet)
      (fun _ ↦ hBoundary)
  · exact coproduct_GW
      (fun _ : SSet.relativeCellComplexOfMono.ι i n ↦ SSet.stdSimplex.{u}.obj ⦋n⦌)
      (fun _ ↦ DaggerActualQWeightedResolutionNaturality.representable_augmentation_GW ⦋n⦌)
  · exact hX

/-- Simultaneous dimension induction proves weakness on every stage of every original object. -/
theorem stages_GW (n : ℕ) : ∀ X : SSet.{u}, GW (augmentation.app ((stages X).obj n)) := by
  induction n with
  | zero => exact zero_GW
  | succ n ih =>
      intro X
      apply successor_GW X n (ih X)
      exact iso_GW (stageIso (SSet.boundary.{u} n).toSSet n)
        (ih (SSet.boundary.{u} n).toSSet)

/-- The original augmentation is weak for every original simplicial set. -/
theorem augmentation_GW (X : SSet.{u}) : GW (augmentation.app X) :=
  DaggerActualQWeightedAugmentationFilteredColimits.sequential_GW (stages X)
    (cocone X) (isColimit X) (fun f ↦ stages_mono X f) (fun n ↦ stages_GW n X)

end
end DaggerActualQWeightedAugmentationSkeletonInduction
