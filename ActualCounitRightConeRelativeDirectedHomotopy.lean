import ActualRigidificationRelativeDirectedHomotopy
import OriginalCounitRightConeRelativeHomotopyTimeOne
import OriginalEnrichedHomRetractRecovered

/-! Apply the directed Hom comparison to the original right-cone deformation. -/

set_option autoImplicit false
open CategoryTheory EnrichedCategory MonoidalCategory CartesianMonoidalCategory
open Opposite Simplicial HomotopicalAlgebra
open DaggerModels.OrdinaryRigidification
open DaggerModels.OrdinaryRigidification.RigidificationVertices
open DaggerChosenRigidificationNecklace hiding thickeningUnit
open DaggerOrdinaryPiZeroCategory DaggerOrdinaryTranslation DaggerSSetGluing
open DaggerOriginalCounitRightCone DaggerOriginalCounitRightConeContractibilityRetraction
open DaggerOriginalCounitRightConeRelativeHomotopy DaggerOriginalEnrichedHomTransport
open DaggerActualRigidificationDirectedIntervalObjects
open scoped SSet.modelCategoryQuillen
universe u

namespace DaggerActualCounitRightConeRelativeDirectedHomotopy

noncomputable section

/-- A map out of the standard point equals its actual constant-vertex extension. -/
theorem vertexMap_const {X Y : SSet.{u}} (v : (Δ[0] : SSet.{u}) ⟶ X) :
    (SSet.const (v.app (op ⦋0⦌) (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 1))) : Y ⟶ X) =
      SSet.stdSimplex.isTerminalObj₀.from Y ≫ v := by
  apply NatTrans.ext
  funext q y
  let f : op ⦋0⦌ ⟶ q := (SimplexCategory.const q.unop ⦋0⦌ 0).op
  have h := congrFun (v.naturality f) (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 1))
  change v.app q ((Δ[0] : SSet.{u}).map f (SSet.stdSimplex.obj₀Equiv.symm 0)) =
    X.map f (v.app (op ⦋0⦌) (SSet.stdSimplex.obj₀Equiv.symm 0)) at h
  change X.map f (v.app (op ⦋0⦌) (SSet.stdSimplex.obj₀Equiv.symm 0)) =
    v.app q ((SSet.stdSimplex.isTerminalObj₀.from Y).app q y)
  rw [← h]
  apply congrArg (v.app q)
  obtain ⟨q⟩ := q
  induction q using SimplexCategory.rec with | _ d =>
    apply SSet.stdSimplex.ext
    intro i
    apply Fin.ext
    omega

/-- The literal cone endpoint map gives the corresponding entire vertical line. -/
theorem vertexLine_endpointMap (n : ℕ) (v : (Δ[0] : SSet.{u}) ⟶ cone n)
    (a : (rigidification.obj (cone n)).Obj)
    (ha : (vertexEquiv (cone n)).symm a =
      v.app (op ⦋0⦌) (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 1))) :
    vertexLine (cone n) a =
      CartesianMonoidalCategory.lift (SSet.stdSimplex.isTerminalObj₀.from Δ[1]) (𝟙 Δ[1]) ≫
        (v ▷ (Δ[1] : SSet.{u})) := by
  apply NatTrans.ext
  funext q x
  change ((SSet.const ((vertexEquiv (cone n)).symm a)).app q x, x) =
    (v.app q ((SSet.stdSimplex.isTerminalObj₀.from Δ[1]).app q x), x)
  rw [ha]
  exact congrArg (fun z => (z, x)) (congrFun (NatTrans.congr_app (vertexMap_const v) q) x)

/-- The original homotopy fixes the full vertical line through the collapsed vertex. -/
theorem alphaLine_fixed (n : ℕ) :
    vertexLine (cone.{u} n) (alphaObj n) ≫ relativeHomotopy n =
      SSet.const ((vertexEquiv (cone n)).symm (alphaObj n)) := by
  have ha : (vertexEquiv (cone n)).symm (alphaObj n) = alpha n :=
    (vertexEquiv (cone n)).symm_apply_apply _
  rw [vertexLine_endpointMap n (alphaMap n) (alphaObj n) ha, Category.assoc,
    alpha_relativeHomotopy]
  rw [ha, alpha, vertexMap_const (alphaMap n)]
  simp only [← Category.assoc]
  congr 1

/-- The same whole-line equation retains the terminal formal cone vertex. -/
theorem omegaLine_fixed (n : ℕ) :
    vertexLine (cone.{u} n) (omegaObj n) ≫ relativeHomotopy n =
      SSet.const ((vertexEquiv (cone n)).symm (omegaObj n)) := by
  have hb : (vertexEquiv (cone n)).symm (omegaObj n) = omega n :=
    (vertexEquiv (cone n)).symm_apply_apply _
  rw [vertexLine_endpointMap n (omegaMap n) (omegaObj n) hb, Category.assoc,
    omega_relativeHomotopy]
  rw [hb, omega, vertexMap_const (omegaMap n)]
  simp only [← Category.assoc]
  congr 1

/-- The actual cone retraction induces W on the original two-endpoint Hom. -/
theorem retraction_hom_GW (n : ℕ) :
    GW ((rigidification.map (projection.{u} n ≫ lastEdge n)).map (alphaObj n) (omegaObj n)) :=
  DaggerActualRigidificationRelativeDirectedHomotopy.endomorphism_GW
    (cone n) (relativeHomotopy n) (projection n ≫ lastEdge n)
    (relativeHomotopy_time_zero n) (relativeHomotopy_time_one n)
    (alphaObj n) (omegaObj n) (alphaLine_fixed n) (omegaLine_fixed n)

/-- The original edge projection is a Hom retract of this same actual retraction. -/
theorem projection_hom_GW (n : ℕ) :
    GW ((rigidification.map (projection.{u} n)).map (alphaObj n) (omegaObj n)) := by
  have hs : rigidification.map (lastEdge.{u} n) ≫ rigidification.map (projection n) =
      𝟙 (rigidification.obj (Δ[1] : SSet.{u})) := by
    rw [← Functor.map_comp, lastEdge_projection, CategoryTheory.Functor.map_id]
  apply DaggerOriginalEnrichedHomRetract.GW_of_retract
    (rigidification.map (projection n)) (rigidification.map (lastEdge n)) hs
  have h : rigidification.map (projection.{u} n) ≫ rigidification.map (lastEdge n) =
      rigidification.map (projection n ≫ lastEdge n) := (Functor.map_comp _ _ _).symm
  exact (GW_functorHom_congr h (alphaObj n) (omegaObj n)).2 (retraction_hom_GW n)

end
end DaggerActualCounitRightConeRelativeDirectedHomotopy
