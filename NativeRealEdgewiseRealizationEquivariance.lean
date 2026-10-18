import NativeRealEdgewiseRealizationComparison
import NativeRealEdgewiseDaggerInvolution
import OriginalDaggerRealizationInvolution

/-! Strict equivariance for the original dagger realization, via the actual adjunction mate. -/
set_option autoImplicit false
open CategoryTheory Opposite DaggerModels
open DaggerNativeRealEdgewiseIndex DaggerNativeRealEdgewiseSSet
open DaggerNativeRealEdgewiseTopologicalParameters
open DaggerNativeRealEdgewiseRealizationComparison DaggerNativeRealEdgewiseDaggerInvolution
open DaggerOriginalDaggerRealizationInvolution DaggerOriginalRealizationOppositeComparison
open DaggerOriginalRealizationReversalCoherence DaggerOriginalSingularSetReversal
universe u
namespace DaggerNativeRealEdgewiseRealizationEquivariance
noncomputable section

theorem unit_realized_dagger (X : DaggerSSet.{u}) :
    sSetTopAdj.unit.app X.toSSet ≫ TopCat.toSSet.map (realizationInvolutionHom X) =
      X.dagger ≫ SSet.opFunctor.map (sSetTopAdj.unit.app X.toSSet) ≫
        singularReversal.hom.app (SSet.toTop.obj X.toSSet) := by
  unfold realizationInvolutionHom
  rw [Functor.map_comp, ← Category.assoc]
  have h := sSetTopAdj.unit.naturality X.dagger
  change X.dagger ≫ sSetTopAdj.unit.app X.toSSet.op =
    sSetTopAdj.unit.app X.toSSet ≫ TopCat.toSSet.map (SSet.toTop.map X.dagger) at h
  rw [← h, Category.assoc, realization_mate]

theorem transpose_equivariant (X : DaggerSSet.{u}) :
    involution X ≫ transpose X.toSSet =
      transpose X.toSSet ≫ TopCat.toSSet.map (realizationInvolutionHom X) := by
  ext n z
  apply ULift.ext
  have h := congrArg
    (fun f : X.toSSet ⟶ TopCat.toSSet.obj (SSet.toTop.obj X.toSSet) ↦
      f.app (epsilon.op.obj n) z) (unit_realized_dagger X)
  have h' := congrArg ULift.down h
  change ((sSetTopAdj.unit.app X.toSSet).app (epsilon.op.obj n) z).down ≫
      realizationInvolutionHom X =
    DaggerOriginalTopologicalSimplexReversal.reversalIso.inv.app (epsilon.obj n.unop) ≫
      ((sSetTopAdj.unit.app X.toSSet).app (epsilon.op.obj n)
        (X.dagger.app (epsilon.op.obj n) z)).down at h'
  change parameterMap.app n.unop ≫
      ((sSetTopAdj.unit.app X.toSSet).app (epsilon.op.obj n)
        (X.dagger.app (epsilon.op.obj n) z)).down =
    (parameterMap.app n.unop ≫
      ((sSetTopAdj.unit.app X.toSSet).app (epsilon.op.obj n) z).down) ≫
        realizationInvolutionHom X
  rw [Category.assoc, h', ← Category.assoc, parameterMap_palindromic_inv]

theorem comparison_equivariant (X : DaggerSSet.{u}) :
    SSet.toTop.map (involution X) ≫ comparison X.toSSet =
      comparison X.toSSet ≫ realizationInvolutionHom X := by
  apply (sSetTopAdj.homEquiv (edgewise.obj X.toSSet) (SSet.toTop.obj X.toSSet)).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  calc
    _ = involution X ≫ (sSetTopAdj.unit.app (edgewise.obj X.toSSet) ≫
        TopCat.toSSet.map (comparison X.toSSet)) := by
      have hn : involution X ≫ sSetTopAdj.unit.app (edgewise.obj X.toSSet) =
          sSetTopAdj.unit.app (edgewise.obj X.toSSet) ≫
            TopCat.toSSet.map (SSet.toTop.map (involution X)) :=
        sSetTopAdj.unit.naturality (involution X)
      rw [← Category.assoc, ← hn]
      rfl
    _ = involution X ≫ transpose X.toSSet := by rw [comparison_mate]
    _ = transpose X.toSSet ≫ TopCat.toSSet.map (realizationInvolutionHom X) :=
      transpose_equivariant X
    _ = _ := by rw [← comparison_mate, Category.assoc]

end
end DaggerNativeRealEdgewiseRealizationEquivariance
