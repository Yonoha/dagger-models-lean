import OriginalCounitRightConeRelativeHomMapEndpointLawsReconciled
import OriginalRigidificationDirectedProductProjectionReconciled

/-!
# Factorization of the original right-cone Hom retraction

The literal cone projection and its last-edge section induce maps between the
original `Q n` and the actual directed Hom of `Δ[1]`. Both endpoint transports
are retained. The resulting composite is the already defined `retractionHom`.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial DaggerChosenRigidificationNecklace
open DaggerOriginalCounitRightCone
open DaggerOriginalCounitRightConeContractibilityRetraction
open DaggerOriginalCounitRightConeRelativeHomotopy
open DaggerOriginalCounitRightConeRelativeHomMapEndpointLaws
open DaggerOriginalRigidificationDirectedProductProjection
open DaggerOriginalChosenHomMapFunctoriality
open DaggerModels.OrdinaryRigidification.DirectedIntervalHom

universe u

namespace DaggerOriginalCounitRightConeRetractionHomFactorization

noncomputable section

private abbrev I : SSet.{u} := Δ[1]

private theorem simplex_map_vertex {m n : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌)
    (i : Fin (m + 1)) :
    (SSet.stdSimplex.map f).app (op ⦋0⦌)
        (SSet.stdSimplex.obj₀Equiv.symm i) =
      SSet.stdSimplex.obj₀Equiv.symm (f.toOrderHom i) := by
  apply SSet.stdSimplex.obj₀Equiv.injective
  rfl

private theorem firstVertex_vertex :
    (SSet.stdSimplex.map firstVertexHom).app (op ⦋0⦌)
        (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 1)) = vertexZero.{u} := by
  rw [simplex_map_vertex]
  change SSet.stdSimplex.obj₀Equiv.symm
      (firstVertexHom.toOrderHom (0 : Fin 1)) =
    SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 2)
  rfl

/-- The cone projection sends the original collapsed endpoint to vertex zero. -/
theorem projection_alpha (n : ℕ) :
    (projection.{u} n).app (op ⦋0⦌) (alpha.{u} n) = vertexZero.{u} := by
  have h := congrArg
    (fun f : (Δ[0] : SSet.{u}) ⟶ I.{u} =>
      f.app (op ⦋0⦌) (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 1)))
    (baseIncl_projection.{u} n)
  simpa only [SSet.comp_app, types_comp_apply, alpha, alphaMap,
    firstVertex_vertex] using h

/-- The last edge starts at the literal collapsed endpoint of the cone. -/
theorem lastEdge_zero (n : ℕ) :
    (lastEdge.{u} n).app (op ⦋0⦌) vertexZero.{u} = alpha.{u} n := by
  have hmap : SSet.stdSimplex.map firstVertexHom ≫ lastEdge.{u} n =
      baseIncl.{u} n := by
    simpa only [lastEdge, Category.assoc] using firstVertex_lastEdge_base.{u} n
  have h := congrArg
    (fun f : (Δ[0] : SSet.{u}) ⟶ cone.{u} n =>
      f.app (op ⦋0⦌) (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 1))) hmap
  simpa only [SSet.comp_app, types_comp_apply, firstVertex_vertex, alpha,
    alphaMap] using h

private theorem lastEdge_one_simplex (n : ℕ) :
    (SSet.stdSimplex.map (lastEdgeHom n)).app (op ⦋0⦌) vertexOne.{u} =
      (lastVertex.{u} n).app (op ⦋0⦌)
        (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 1)) := by
  apply SSet.stdSimplex.obj₀Equiv.injective
  change (lastEdgeHom n).toOrderHom (1 : Fin 2) = Fin.last (n + 1)
  rfl

/-- The last edge ends at the original terminal endpoint of the cone. -/
theorem lastEdge_one (n : ℕ) :
    (lastEdge.{u} n).app (op ⦋0⦌) vertexOne.{u} = omega.{u} n := by
  change (simplexIncl.{u} n).app (op ⦋0⦌)
      ((SSet.stdSimplex.map (lastEdgeHom n)).app (op ⦋0⦌) vertexOne.{u}) =
    (simplexIncl.{u} n).app (op ⦋0⦌)
      ((lastVertex.{u} n).app (op ⦋0⦌)
        (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 1)))
  exact congrArg ((simplexIncl.{u} n).app (op ⦋0⦌)) (lastEdge_one_simplex.{u} n)

/-- The cone projection sends the original terminal endpoint to vertex one. -/
theorem projection_omega (n : ℕ) :
    (projection.{u} n).app (op ⦋0⦌) (omega.{u} n) = vertexOne.{u} := by
  have h := congrArg
    (fun f : I.{u} ⟶ I.{u} => f.app (op ⦋0⦌) vertexOne.{u})
    (lastEdge_projection.{u} n)
  simpa only [SSet.comp_app, types_comp_apply, lastEdge_one, types_id_apply] using h

/-- The original cone-Hom map induced by the literal projection to `Δ[1]`. -/
def projectionHomMap (n : ℕ) : Q.{u} n ⟶ intervalHom.{u} :=
  originalChosenHomMap (projection.{u} n) (alpha.{u} n) (omega.{u} n) ≫
    targetHomTransport
      (congrArg (RV I.{u}) (projection_alpha.{u} n))
      (congrArg (RV I.{u}) (projection_omega.{u} n))

/-- The original Hom map induced by the literal last edge of the cone. -/
def lastEdgeHomMap (n : ℕ) : intervalHom.{u} ⟶ Q.{u} n :=
  originalChosenHomMap (lastEdge.{u} n) vertexZero.{u} vertexOne.{u} ≫
    targetHomTransport
      (congrArg (RV (cone.{u} n)) (lastEdge_zero.{u} n))
      (congrArg (RV (cone.{u} n)) (lastEdge_one.{u} n))

private theorem map_comp_fixed {A B C : SSet.{u}} (f : A ⟶ B) (g : B ⟶ C)
    (a b : A.obj (op ⦋0⦌)) (c d : B.obj (op ⦋0⦌)) (e h : C.obj (op ⦋0⦌))
    (hfc : f.app (op ⦋0⦌) a = c) (hfd : f.app (op ⦋0⦌) b = d)
    (hgc : g.app (op ⦋0⦌) c = e) (hgd : g.app (op ⦋0⦌) d = h)
    (hfgc : (f ≫ g).app (op ⦋0⦌) a = e)
    (hfgd : (f ≫ g).app (op ⦋0⦌) b = h) :
    (originalChosenHomMap f a b ≫
        targetHomTransport (congrArg (RV B) hfc) (congrArg (RV B) hfd)) ≫
      (originalChosenHomMap g c d ≫
        targetHomTransport (congrArg (RV C) hgc) (congrArg (RV C) hgd)) =
    originalChosenHomMap (f ≫ g) a b ≫
      targetHomTransport (congrArg (RV C) hfgc) (congrArg (RV C) hfgd) := by
  cases hfc
  cases hfd
  rw [originalChosenHomMap_comp]
  simp only [SSet.comp_app, types_comp_apply, targetHomTransport, eqToHom_refl,
    Category.comp_id, Category.assoc]

/-- The existing original retraction Hom factors through the actual directed interval Hom. -/
theorem retractionHom_factor (n : ℕ) :
    retractionHom.{u} n =
      projectionHomMap.{u} n ≫ lastEdgeHomMap.{u} n := by
  have hα : (projection.{u} n ≫ lastEdge.{u} n).app (op ⦋0⦌)
      (alpha.{u} n) = alpha.{u} n := by
    simp only [SSet.comp_app, types_comp_apply, projection_alpha, lastEdge_zero]
  have hω : (projection.{u} n ≫ lastEdge.{u} n).app (op ⦋0⦌)
      (omega.{u} n) = omega.{u} n := by
    simp only [SSet.comp_app, types_comp_apply, projection_omega, lastEdge_one]
  unfold projectionHomMap lastEdgeHomMap retractionHom
  simpa only [Category.assoc] using
    (map_comp_fixed (projection.{u} n) (lastEdge.{u} n)
      (alpha.{u} n) (omega.{u} n) vertexZero.{u} vertexOne.{u}
      (alpha.{u} n) (omega.{u} n)
      (projection_alpha.{u} n) (projection_omega.{u} n)
      (lastEdge_zero.{u} n) (lastEdge_one.{u} n) hα hω).symm

end

end DaggerOriginalCounitRightConeRetractionHomFactorization
