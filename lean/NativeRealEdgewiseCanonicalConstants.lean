import NativeRealEdgewiseHomotopyFixedPointComparison
import NativeRealEdgewiseRealizationVertices
import NativeRealEdgewiseC2Action

/-! Literal equivariant constants at the ORIGINAL edgewise vertices and their exact images. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial DaggerModels
open DaggerNativeRealEdgewiseSSet DaggerNativeRealEdgewiseRealizationVertices
open DaggerNativeRealEdgewiseContinuousComparison
open DaggerNativeRealEdgewiseHomotopyFixedPointComparison
open DaggerOriginalDaggerRealizationC2Action DaggerOriginalDaggerRealizationContinuousAction
open DaggerOriginalEquivariantConstantMaps DaggerOriginalEC2RealizationAction
open DaggerOriginalEC2HomotopyFixedPointObject DaggerOriginalEC2HomotopyFixedPointFunctor
universe u
namespace DaggerNativeRealEdgewiseCanonicalConstants
noncomputable section

theorem edgewiseRealizedVertex_fixed (X : DaggerSSet.{u}) (x : X.toSSet _⦋0⦌) (g : C2.{u}) :
    ((realizedEdgewiseContinuousFunctor.obj X).obj.ρ g).asHom (edgewiseRealizedVertex X x) =
      edgewiseRealizedVertex X x := by
  have hc := ((SSet.toTop.mapAction C2.{u}).map
    (DaggerNativeRealEdgewiseC2Action.fixedVertexMap X x)).comm g
  change SSet.toTop.map (𝟙 (Δ[0] : SSet.{u})) ≫
      SSet.toTop.map (DaggerNativeRealEdgewiseDaggerInvolution.vertexMap X x) =
    SSet.toTop.map (DaggerNativeRealEdgewiseDaggerInvolution.vertexMap X x) ≫
      ((realizedEdgewiseContinuousFunctor.obj X).obj.ρ g).asHom at hc
  rw [CategoryTheory.Functor.map_id, Category.id_comp] at hc
  exact congrArg (fun f : SSet.toTop.obj (Δ[0] : SSet.{u}) ⟶
      SSet.toTop.obj (edgewise.obj X.toSSet) ↦
    f ((SSet.toTopSimplex.{u}.inv.app ⦋0⦌)
      (default : SimplexCategory.toTop.{u}.obj ⦋0⦌))) hc.symm

theorem vertexMap_natural {X Y : DaggerSSet.{u}} (f : X ⟶ Y) (x : X.toSSet _⦋0⦌) :
    DaggerNativeRealEdgewiseDaggerInvolution.vertexMap X x ≫ edgewise.map f.hom =
      DaggerNativeRealEdgewiseDaggerInvolution.vertexMap Y (f.hom.app (op ⦋0⦌) x) := by
  unfold DaggerNativeRealEdgewiseDaggerInvolution.vertexMap
  rw [SSet.yonedaEquiv_symm_comp]
  apply congrArg SSet.yonedaEquiv.symm
  have h := congrArg
    (fun k : X.toSSet _⦋0⦌ ⟶ Y.toSSet _⦋1⦌ ↦ k x)
    (f.hom.naturality (SimplexCategory.σ (0 : Fin 1)).op)
  change f.hom.app (op ⦋1⦌) (X.toSSet.σ (0 : Fin 1) x) =
    Y.toSSet.σ (0 : Fin 1) (f.hom.app (op ⦋0⦌) x) at h ⊢
  exact h

theorem edgewiseRealizedVertex_natural {X Y : DaggerSSet.{u}} (f : X ⟶ Y)
    (x : X.toSSet _⦋0⦌) :
    SSet.toTop.map (edgewise.map f.hom) (edgewiseRealizedVertex X x) =
      edgewiseRealizedVertex Y (f.hom.app (op ⦋0⦌) x) := by
  have h := congrArg SSet.toTop.map (vertexMap_natural f x)
  rw [CategoryTheory.Functor.map_comp] at h
  exact congrArg (fun k : SSet.toTop.obj (Δ[0] : SSet.{u}) ⟶
      SSet.toTop.obj (edgewise.obj Y.toSSet) ↦
    k ((SSet.toTopSimplex.{u}.inv.app ⦋0⦌)
      (default : SimplexCategory.toTop.{u}.obj ⦋0⦌))) h

def edgewiseFixedPoint (X : DaggerSSet.{u}) (x : X.toSSet _⦋0⦌) :
    FixedPoints (realizedEdgewiseContinuousFunctor.obj X) :=
  ⟨edgewiseRealizedVertex X x, edgewiseRealizedVertex_fixed X x⟩

def edgewiseConstantMap (X : DaggerSSet.{u}) (x : X.toSSet _⦋0⦌) :
    EquivariantMaps realizedEC2ContinuousAction.{u} (realizedEdgewiseContinuousFunctor.obj X) :=
  constantMap _ _ (edgewiseFixedPoint X x)

def edgewiseCanonicalZero (X : DaggerSSet.{u}) (x : X.toSSet _⦋0⦌) :
    (edgewiseHomotopyFixedPointFunctor.obj X).obj (op ⦋0⦌) :=
  (TopCat.toSSetObjEquiv
    (mappingTop (realizedEdgewiseContinuousFunctor.obj X)) (op ⦋0⦌)).symm
      (ContinuousMap.const _ (edgewiseConstantMap X x))

theorem canonicalZero_comparison (X : DaggerSSet.{u}) (x : X.toSSet _⦋0⦌) :
    (homotopyFixedPointComparison.app X).app (op ⦋0⦌) (edgewiseCanonicalZero X x) =
      canonicalZeroSimplex X x := by
  apply (TopCat.toSSetObjEquiv
    (mappingTop (realizedContinuousActionFunctor.obj X)) (op ⦋0⦌)).injective
  ext t
  apply Subtype.ext
  ext e
  change (continuousComparison X).hom.hom (edgewiseRealizedVertex X x) =
    DaggerOriginalDaggerRealizationVertices.realizedVertex X x
  exact DaggerNativeRealEdgewiseRealizationC2Comparison.comparisonActionMap_vertex X x

theorem edgewiseCanonicalZero_natural {X Y : DaggerSSet.{u}} (f : X ⟶ Y)
    (x : X.toSSet _⦋0⦌) :
    (edgewiseHomotopyFixedPointFunctor.map f).app (op ⦋0⦌) (edgewiseCanonicalZero X x) =
      edgewiseCanonicalZero Y (f.hom.app (op ⦋0⦌) x) := by
  apply (TopCat.toSSetObjEquiv
    (mappingTop (realizedEdgewiseContinuousFunctor.obj Y)) (op ⦋0⦌)).injective
  ext t
  apply Subtype.ext
  ext e
  change SSet.toTop.map (edgewise.map f.hom) (edgewiseRealizedVertex X x) =
    edgewiseRealizedVertex Y (f.hom.app (op ⦋0⦌) x)
  exact edgewiseRealizedVertex_natural f x

end
end DaggerNativeRealEdgewiseCanonicalConstants
