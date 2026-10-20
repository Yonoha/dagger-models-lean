import NativeRealEdgewiseTargetClosure
import NativeRealEdgewiseStandardSimplexWeak
import NativeSimplicialSkeletonStages

/-! The literal edgewise target projection is weak for every original simplicial set. -/
set_option autoImplicit false
open CategoryTheory Limits Simplicial HomotopicalAlgebra
open DaggerSSetGluing DaggerNativeRealEdgewiseSSet DaggerNativeRealEdgewiseExactness
open DaggerNativeRealEdgewiseTargetClosure DaggerNativeSimplicialSkeletonStages
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeRealEdgewiseTargetWeak
noncomputable section

theorem zero_GW (X : SSet.{u}) : GW (targetNatural.app ((stages X).obj 0)) :=
  iso_GW (SSet.relativeCellComplex X).toTransfiniteCompositionOfShape.isoBot.symm
    (initial_GW _ SSet.Subcomplex.isInitialBot)

theorem successor_GW (X : SSet.{u}) (n : ℕ)
    (hX : GW (targetNatural.app ((stages X).obj n)))
    (hBoundary : GW (targetNatural.app (SSet.boundary.{u} n).toSSet)) :
    GW (targetNatural.app ((stages X).obj (n + 1))) := by
  let i := (⊥ : X.Subcomplex).ι
  apply pushout_GW (SSet.relativeCellComplexOfMono.m i n)
    (SSet.relativeCellComplexOfMono.t i n) (SSet.relativeCellComplexOfMono.b i n)
    (SSet.relativeCellComplexOfMono.r i n) (SSet.relativeCellComplexOfMono.isPushout i n).flip
  · exact coproduct_GW
      (fun _ : SSet.relativeCellComplexOfMono.ι i n ↦ (SSet.boundary.{u} n).toSSet)
      (fun _ ↦ hBoundary)
  · exact coproduct_GW
      (fun _ : SSet.relativeCellComplexOfMono.ι i n ↦ SSet.stdSimplex.{u}.obj ⦋n⦌)
      (fun _ ↦ DaggerNativeRealEdgewiseStandardSimplexWeak.targetProjection_GW n)
  · exact hX

theorem stages_GW (n : ℕ) : ∀ X : SSet.{u}, GW (targetNatural.app ((stages X).obj n)) := by
  induction n with
  | zero => exact zero_GW
  | succ n ih =>
      intro X
      apply successor_GW X n (ih X)
      exact iso_GW (stageIso (SSet.boundary.{u} n).toSSet n)
        (ih (SSet.boundary.{u} n).toSSet)

theorem targetProjection_GW (X : SSet.{u}) : GW (targetProjection X) :=
  sequential_GW (stages X) (cocone X) (isColimit X)
    (fun f ↦ stages_mono X f) (fun n ↦ stages_GW n X)

theorem targetProjection_weak (X : SSet.{u}) : WeakEquivalence (targetProjection X) :=
  (weakEquivalence_iff_GW _).mpr (targetProjection_GW X)

end
end DaggerNativeRealEdgewiseTargetWeak
