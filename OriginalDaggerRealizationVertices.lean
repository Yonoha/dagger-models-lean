import OriginalDaggerRealizationInvolution
import Mathlib.AlgebraicTopology.TopologicalSimplex

/-!
# Original vertices are fixed by the actual realized dagger

The point is the image of the literal Yoneda vertex under Mathlib's
realization of `Δ[0]`. No coend coordinates or new topological action are used.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerModels
open DaggerOriginalDaggerRealizationInvolution
open DaggerOriginalRealizationOppositeComparison

universe u

namespace DaggerOriginalDaggerRealizationVertices

noncomputable section

private abbrev O : SSet.{u} ⥤ SSet.{u} := SSet.opFunctor.{u}
private abbrev R : SSet.{u} ⥤ TopCat.{u} := SSet.toTop.{u}

/-- The actual Yoneda map represented by an original zero-simplex. -/
def vertexMap (X : DaggerSSet.{u}) (x : X.toSSet _⦋0⦌) :
    (Δ[0] : SSet.{u}) ⟶ X.toSSet :=
  SSet.yonedaEquiv.symm x

private def zeroVertex : (Δ[0] : SSet.{u}) _⦋0⦌ :=
  SSet.stdSimplex.obj₀Equiv.symm 0

private def zeroOpMap : (Δ[0] : SSet.{u}) ⟶ O.obj (Δ[0] : SSet.{u}) :=
  SSet.yonedaEquiv.symm (SSet.opObjEquiv.symm zeroVertex)

private theorem vertexMap_dagger (X : DaggerSSet.{u})
    (x : X.toSSet _⦋0⦌) :
    vertexMap X x ≫ X.dagger =
      zeroOpMap.{u} ≫ O.map (vertexMap X x) := by
  apply SSet.yonedaEquiv.injective
  apply SSet.opObjEquiv.injective
  have hz : zeroVertex.{u} = SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u})) := by
    apply SSet.stdSimplex.obj₀Equiv.injective
    apply Fin.ext
    omega
  have hv : (vertexMap X x).app (op ⦋0⦌) zeroVertex = x := by
    rw [hz, ← SSet.yonedaEquiv_comp, Category.id_comp]
    exact SSet.yonedaEquiv.apply_symm_apply x
  simpa [vertexMap, zeroOpMap, zeroVertex, SSet.yonedaEquiv_comp,
    SSet.opFunctor_map] using (X.fixedVertices x).trans hv.symm

private theorem zeroRealization_id :
    R.map (zeroOpMap.{u}) ≫
      realizationOppositeIso.hom.app (Δ[0] : SSet.{u}) =
        𝟙 (R.obj (Δ[0] : SSet.{u})) := by
  apply (cancel_mono (SSet.toTopSimplex.{u}.hom.app ⦋0⦌)).1
  ext z
  exact Subsingleton.elim _ _

/-- The whole realized vertex map commutes with the involution trivially. -/
theorem realizedVertexMap_fixed (X : DaggerSSet.{u})
    (x : X.toSSet _⦋0⦌) :
    R.map (vertexMap X x) ≫ realizationInvolutionHom X =
      R.map (vertexMap X x) := by
  let v := vertexMap X x
  let r := realizationOppositeIso.{u}
  have hn : R.map (O.map v) ≫ r.hom.app X.toSSet =
      r.hom.app (Δ[0] : SSet.{u}) ≫ R.map v := by
    simpa only [CategoryTheory.Functor.comp_map] using r.hom.naturality v
  calc
    R.map v ≫ realizationInvolutionHom X =
        R.map (v ≫ X.dagger) ≫ r.hom.app X.toSSet := by
      simp only [realizationInvolutionHom, CategoryTheory.Functor.map_comp, Category.assoc]
      rfl
    _ = R.map (zeroOpMap.{u} ≫ O.map v) ≫ r.hom.app X.toSSet := by
      rw [vertexMap_dagger X x]
    _ = R.map zeroOpMap ≫
          (R.map (O.map v) ≫ r.hom.app X.toSSet) := by
      simp only [CategoryTheory.Functor.map_comp, Category.assoc]
    _ = (R.map zeroOpMap ≫ r.hom.app (Δ[0] : SSet.{u})) ≫
          R.map v := by
      rw [hn]
      simp only [Category.assoc]
    _ = R.map v := by
      rw [zeroRealization_id, Category.id_comp]

private def zeroRealizationPoint : R.obj (Δ[0] : SSet.{u}) :=
  (SSet.toTopSimplex.{u}.inv.app ⦋0⦌)
    (default : SimplexCategory.toTop.{u}.obj ⦋0⦌)

/-- The actual point of realization represented by the original vertex. -/
def realizedVertex (X : DaggerSSet.{u}) (x : X.toSSet _⦋0⦌) :
    R.obj X.toSSet :=
  (R.map (vertexMap X x)) zeroRealizationPoint

/-- Every original vertex gives a fixed point in the realized space. -/
theorem realizedVertex_fixed (X : DaggerSSet.{u})
    (x : X.toSSet _⦋0⦌) :
    realizationInvolutionHom X (realizedVertex X x) = realizedVertex X x := by
  have h := congrArg
    (fun g : R.obj (Δ[0] : SSet.{u}) ⟶ R.obj X.toSSet ↦
      g zeroRealizationPoint) (realizedVertexMap_fixed X x)
  simpa only [realizedVertex, ConcreteCategory.comp_apply] using h

end

end DaggerOriginalDaggerRealizationVertices
