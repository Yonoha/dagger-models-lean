import NativeRealEdgewiseRealizationEquivariance
import NativeRealEdgewiseRealizationVertices
import NativeRealEdgewiseC2Action

/-! The actual original C2-equivariant natural comparison, with original vertex anchors. -/
set_option autoImplicit false
open CategoryTheory DaggerModels Simplicial
open DaggerNativeRealEdgewiseRealizationComparison
open DaggerNativeRealEdgewiseRealizationEquivariance
open DaggerNativeRealEdgewiseRealizationVertices
open DaggerOriginalDaggerRealizationC2Action DaggerOriginalCompletedDaggerMappingAction
universe u
namespace DaggerNativeRealEdgewiseRealizationC2Comparison
noncomputable section

def realizedEdgewiseFunctor : DaggerSSet.{u} ⥤ Action TopCat.{u} C2.{u} :=
  DaggerNativeRealEdgewiseC2Action.functor ⋙ SSet.toTop.mapAction C2.{u}

def comparisonActionMap (X : DaggerSSet.{u}) :
    realizedEdgewiseFunctor.obj X ⟶ realizedAction X where
  hom := comparison X.toSSet
  comm g := by
    rcases originalC2_cases g with rfl | rfl
    · simp
    · change SSet.toTop.map (((DaggerNativeRealEdgewiseC2Action.action X).ρ generator).asHom) ≫
        comparison X.toSSet = comparison X.toSSet ≫
          DaggerOriginalDaggerRealizationInvolution.realizationInvolutionHom X
      rw [DaggerNativeRealEdgewiseC2Action.action_generator]
      exact comparison_equivariant X

theorem comparisonActionMap_hom (X : DaggerSSet.{u}) :
    (comparisonActionMap X).hom = comparison X.toSSet := rfl

def naturalActionComparison : realizedEdgewiseFunctor ⟶ realizedActionFunctor where
  app := comparisonActionMap
  naturality X Y f := by
    apply Action.hom_ext
    exact comparison_natural f.hom

theorem comparisonActionMap_vertex (X : DaggerSSet.{u}) (x : X.toSSet _⦋0⦌) :
    (comparisonActionMap X).hom (edgewiseRealizedVertex X x) =
      DaggerOriginalDaggerRealizationVertices.realizedVertex X x :=
  realizedVertex_comparison X x

end
end DaggerNativeRealEdgewiseRealizationC2Comparison
