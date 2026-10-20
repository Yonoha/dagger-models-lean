import OriginalStrictPathFiberVertices
import TopCatModelCategory.TopCat.Adj

/-!
# Original singular strict path vertices and continuous paths

The fixed native topological one-simplex homeomorphism identifies actual singular edges with
continuous paths in the same original space, retaining both original endpoint equations.
Composition with the exact strict-fiber vertex equivalence gives the same comparison for the
original singular endpoint fiber. This is a comparison of vertices, not a simplicial equivalence.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerOriginalFullVertexSubcomplex DaggerOriginalStrictPathFiberVertices

universe u

namespace DaggerOriginalSingularStrictPaths

noncomputable section

/-- The actual original singular edge determines a continuous path with the same endpoints. -/
def pathOfSingularEdge (T : TopCat.{u})
    {a b : (TopCat.toSSet.obj T).obj (op ⦋0⦌)} (e : SSet.Edge a b) :
    _root_.Path (TopCat.toSSetObj₀Equiv a) (TopCat.toSSetObj₀Equiv b) where
  toContinuousMap := (TopCat.toSSetObjEquiv T (op ⦋1⦌) e.edge).comp
    ⟨fun t ↦ SSet.stdSimplex.simplexCategoryToTopObjHomeoUnitInterval.{u}.symm (ULift.up t),
      SSet.stdSimplex.simplexCategoryToTopObjHomeoUnitInterval.{u}.symm.continuous_toFun.comp
        continuous_uliftUp⟩
  source' := by
    change (TopCat.toSSetObjEquiv T (op ⦋1⦌) e.edge)
      (SSet.stdSimplex.simplexCategoryToTopObjHomeoUnitInterval.{u}.symm 0) = _
    rw [← TopCat.toSSetObj₀Equiv_toSSet_obj_δ_one, e.src_eq]
  target' := by
    change (TopCat.toSSetObjEquiv T (op ⦋1⦌) e.edge)
      (SSet.stdSimplex.simplexCategoryToTopObjHomeoUnitInterval.{u}.symm 1) = _
    rw [← TopCat.toSSetObj₀Equiv_toSSet_obj_δ_zero, e.tgt_eq]

/-- An actual continuous path gives the original singular edge with exactly its two endpoints. -/
def singularEdgeOfPath (T : TopCat.{u})
    {a b : (TopCat.toSSet.obj T).obj (op ⦋0⦌)}
    (p : _root_.Path (TopCat.toSSetObj₀Equiv a) (TopCat.toSSetObj₀Equiv b)) :
    SSet.Edge a b where
  edge := (TopCat.toSSetObjEquiv T (op ⦋1⦌)).symm
    (p.toContinuousMap.comp
      ⟨fun s ↦ (SSet.stdSimplex.simplexCategoryToTopObjHomeoUnitInterval.{u} s).down,
        continuous_uliftDown.comp
          SSet.stdSimplex.simplexCategoryToTopObjHomeoUnitInterval.{u}.continuous_toFun⟩)
  src_eq := by
    change SimplicialObject.δ (TopCat.toSSet.obj T) (1 : Fin 2) _ = a
    apply TopCat.toSSetObj₀Equiv.injective
    rw [TopCat.toSSetObj₀Equiv_toSSet_obj_δ_one, Equiv.apply_symm_apply]
    change p
      (SSet.stdSimplex.simplexCategoryToTopObjHomeoUnitInterval.{u}
        (SSet.stdSimplex.simplexCategoryToTopObjHomeoUnitInterval.{u}.symm 0)).down = _
    rw [Homeomorph.apply_symm_apply]
    exact p.source
  tgt_eq := by
    change SimplicialObject.δ (TopCat.toSSet.obj T) (0 : Fin 2) _ = b
    apply TopCat.toSSetObj₀Equiv.injective
    rw [TopCat.toSSetObj₀Equiv_toSSet_obj_δ_zero, Equiv.apply_symm_apply]
    change p
      (SSet.stdSimplex.simplexCategoryToTopObjHomeoUnitInterval.{u}
        (SSet.stdSimplex.simplexCategoryToTopObjHomeoUnitInterval.{u}.symm 1)).down = _
    rw [Homeomorph.apply_symm_apply]
    exact p.target

/-- The native singular edges and continuous paths agree, without changing either endpoint. -/
def singularEdgePathEquiv (T : TopCat.{u})
    (a b : (TopCat.toSSet.obj T).obj (op ⦋0⦌)) :
    SSet.Edge a b ≃ _root_.Path (TopCat.toSSetObj₀Equiv a) (TopCat.toSSetObj₀Equiv b) where
  toFun := pathOfSingularEdge T
  invFun := singularEdgeOfPath T
  left_inv e := by
    apply SSet.Edge.ext
    apply (TopCat.toSSetObjEquiv T (op ⦋1⦌)).injective
    simp only [singularEdgeOfPath]
    apply ContinuousMap.ext
    intro s
    change (TopCat.toSSetObjEquiv T (op ⦋1⦌) e.edge)
      (SSet.stdSimplex.simplexCategoryToTopObjHomeoUnitInterval.{u}.symm
        (ULift.up (SSet.stdSimplex.simplexCategoryToTopObjHomeoUnitInterval.{u} s).down)) = _
    rw [ULift.up_down, Homeomorph.symm_apply_apply]
  right_inv p := by
    apply Path.ext
    funext t
    change ((TopCat.toSSetObjEquiv T (op ⦋1⦌))
      ((TopCat.toSSetObjEquiv T (op ⦋1⦌)).symm _))
        (SSet.stdSimplex.simplexCategoryToTopObjHomeoUnitInterval.{u}.symm (ULift.up t)) = p t
    rw [Equiv.apply_symm_apply]
    change p
      (SSet.stdSimplex.simplexCategoryToTopObjHomeoUnitInterval.{u}
        (SSet.stdSimplex.simplexCategoryToTopObjHomeoUnitInterval.{u}.symm (ULift.up t))).down = _
    rw [Homeomorph.apply_symm_apply]

/-- Vertices of the literal singular endpoint fiber are actual continuous paths. -/
def singularStrictPathVertexEquiv (T : TopCat.{u})
    (a b : (TopCat.toSSet.obj T).obj (op ⦋0⦌)) :
    (strictPathFiber (TopCat.toSSet.obj T) a b : SSet).obj (op ⦋0⦌) ≃
      _root_.Path (TopCat.toSSetObj₀Equiv a) (TopCat.toSSetObj₀Equiv b) :=
  (strictPathVertexEquiv (TopCat.toSSet.obj T) a b).trans (singularEdgePathEquiv T a b)

/-- Existence of a literal singular strict path vertex is existence of a continuous path. -/
theorem singularStrictPath_vertex_nonempty_iff (T : TopCat.{u})
    (a b : (TopCat.toSSet.obj T).obj (op ⦋0⦌)) :
    Nonempty ((strictPathFiber (TopCat.toSSet.obj T) a b : SSet).obj (op ⦋0⦌)) ↔
      Nonempty (_root_.Path (TopCat.toSSetObj₀Equiv a) (TopCat.toSSetObj₀Equiv b)) :=
  (singularStrictPathVertexEquiv T a b).nonempty_congr

end

end DaggerOriginalSingularStrictPaths
