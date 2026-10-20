import NativeRealEdgewiseRealizationComparison
import NativeRealEdgewiseDaggerInvolution
import OriginalDaggerRealizationVertices

/-! The comparison preserves the literal original vertex maps, including repeated labels. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial DaggerModels
open DaggerNativeRealEdgewiseSSet DaggerNativeRealEdgewiseRealizationComparison
universe u
namespace DaggerNativeRealEdgewiseRealizationVertices
noncomputable section

def zeroEdgewiseVertexMap : (Δ[0] : SSet.{u}) ⟶ edgewise.obj (Δ[0] : SSet.{u}) :=
  SSet.yonedaEquiv.symm ((Δ[0] : SSet.{u}).σ (0 : Fin 1)
    (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u}))))

theorem vertexMap_factor (X : DaggerSSet.{u}) (x : X.toSSet _⦋0⦌) :
    DaggerNativeRealEdgewiseDaggerInvolution.vertexMap X x =
      zeroEdgewiseVertexMap ≫
        edgewise.map (DaggerOriginalDaggerRealizationVertices.vertexMap X x) := by
  let v := DaggerOriginalDaggerRealizationVertices.vertexMap X x
  have hv : v.app (op ⦋0⦌) (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u}))) = x := by
    rw [← SSet.yonedaEquiv_comp, Category.id_comp]
    exact SSet.yonedaEquiv.apply_symm_apply x
  unfold zeroEdgewiseVertexMap
  rw [SSet.yonedaEquiv_symm_comp]
  apply congrArg SSet.yonedaEquiv.symm
  have h := congrArg
    (fun f : (Δ[0] : SSet.{u}) _⦋0⦌ ⟶ X.toSSet _⦋1⦌ ↦
      f (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u}))))
    (v.naturality (SimplexCategory.σ (0 : Fin 1)).op)
  change X.toSSet.σ (0 : Fin 1) x =
    v.app (op ⦋1⦌) ((Δ[0] : SSet.{u}).σ (0 : Fin 1)
      (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u}))))
  change v.app (op ⦋1⦌) ((Δ[0] : SSet.{u}).σ (0 : Fin 1)
      (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u})))) =
    X.toSSet.σ (0 : Fin 1) (v.app (op ⦋0⦌)
      (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u})))) at h
  rw [hv] at h
  exact h.symm

theorem zeroEdgewiseVertexMap_comparison :
    SSet.toTop.map zeroEdgewiseVertexMap.{u} ≫ comparison (Δ[0] : SSet.{u}) =
      𝟙 (SSet.toTop.obj (Δ[0] : SSet.{u})) := by
  apply (cancel_mono (SSet.toTopSimplex.{u}.hom.app ⦋0⦌)).1
  ext z
  exact Subsingleton.elim _ _

theorem realizedVertexMap_comparison (X : DaggerSSet.{u}) (x : X.toSSet _⦋0⦌) :
    SSet.toTop.map (DaggerNativeRealEdgewiseDaggerInvolution.vertexMap X x) ≫
      comparison X.toSSet =
        SSet.toTop.map (DaggerOriginalDaggerRealizationVertices.vertexMap X x) := by
  rw [vertexMap_factor, Functor.map_comp, Category.assoc, comparison_natural,
    ← Category.assoc, zeroEdgewiseVertexMap_comparison, Category.id_comp]

def edgewiseRealizedVertex (X : DaggerSSet.{u}) (x : X.toSSet _⦋0⦌) :
    SSet.toTop.obj (edgewise.obj X.toSSet) :=
  SSet.toTop.map (DaggerNativeRealEdgewiseDaggerInvolution.vertexMap X x)
    ((SSet.toTopSimplex.{u}.inv.app ⦋0⦌) (default : SimplexCategory.toTop.{u}.obj ⦋0⦌))

theorem realizedVertex_comparison (X : DaggerSSet.{u}) (x : X.toSSet _⦋0⦌) :
    comparison X.toSSet (edgewiseRealizedVertex X x) =
      DaggerOriginalDaggerRealizationVertices.realizedVertex X x := by
  exact congrArg (fun f : SSet.toTop.obj (Δ[0] : SSet.{u}) ⟶ SSet.toTop.obj X.toSSet ↦
    f ((SSet.toTopSimplex.{u}.inv.app ⦋0⦌)
      (default : SimplexCategory.toTop.{u}.obj ⦋0⦌))) (realizedVertexMap_comparison X x)

end
end DaggerNativeRealEdgewiseRealizationVertices
