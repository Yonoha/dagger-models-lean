import ActualCounitRightConeRelativeDirectedHomotopy

/-! Weak contractibility of every original right-cone rigidification Hom Q[n]. -/

set_option autoImplicit false
open CategoryTheory EnrichedCategory MonoidalCategory CartesianMonoidalCategory
open Opposite Simplicial HomotopicalAlgebra
open DaggerModels.OrdinaryRigidification
open DaggerModels.OrdinaryRigidification.RigidificationVertices
open DaggerOriginalCounitRightCone DaggerOriginalCounitRightConeContractibilityRetraction
open DaggerOriginalCounitRightConeFunctor
open DaggerActualRigidificationDirectedIntervalObjects
open DaggerOriginalProductGadget DaggerSSetGluing
open scoped SSet.modelCategoryQuillen
universe u

namespace DaggerActualCounitRightConeHomContractibility

noncomputable section

/-- The actual projection sends the collapsed cone object to the initial edge object. -/
theorem projection_alpha_obj (n : ℕ) :
    (rigidification.map (projection.{u} n)).obj (alphaObj n) = endpoint 0 := by
  rw [alphaObj, vertexEquiv_naturality]
  apply congrArg (vertexEquiv Δ[1])
  change (alphaMap n ≫ projection n).app (op ⦋0⦌)
    (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 1)) = SSet.stdSimplex.obj₀Equiv.symm 0
  rw [alphaMap, baseIncl_projection]
  apply SSet.stdSimplex.obj₀Equiv.injective
  change firstVertexHom.toOrderHom 0 = (0 : Fin 2)
  rw [firstVertexHom]
  rfl

/-- The last formal cone vertex retains the final edge object under the same projection. -/
theorem projection_omega_obj (n : ℕ) :
    (rigidification.map (projection.{u} n)).obj (omegaObj n) = endpoint 1 := by
  rw [omegaObj, vertexEquiv_naturality]
  apply congrArg (vertexEquiv Δ[1])
  change (omegaMap n ≫ projection n).app (op ⦋0⦌)
    (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 1)) = SSet.stdSimplex.obj₀Equiv.symm 1
  have h := AugmentedSimplexCategory.inr_comp_tensorHom
    (AugmentedSimplexCategory.inclusion.map (SimplexCategory.isTerminalZero.from ⦋n⦌))
    (𝟙 (AugmentedSimplexCategory.inclusion.obj ⦋0⦌))
  change AugmentedSimplexCategory.inr' ⦋n⦌ ⦋0⦌ ≫ projectionHom n =
    𝟙 ⦋0⦌ ≫ AugmentedSimplexCategory.inr' ⦋0⦌ ⦋0⦌ at h
  simp only [Category.id_comp] at h
  rw [omegaMap, lastVertex_eq_inr, Category.assoc, simplexIncl_projection,
    ← Functor.map_comp, h]
  apply SSet.stdSimplex.obj₀Equiv.injective
  change (AugmentedSimplexCategory.inr' ⦋0⦌ ⦋0⦌).toOrderHom 0 = (1 : Fin 2)
  rw [AugmentedSimplexCategory.inr'_eval]
  rfl

/-- Collapse of the literal Q[n] is weak, with no contractibility hypothesis supplied. -/
theorem Q_toUnit_GW (n : ℕ) : GW (toUnit (Q.{u} n)) := by
  let p := (rigidification.map (projection.{u} n)).map (alphaObj n) (omegaObj n)
  let Y : SSet.{u} := ((rigidification.map (projection.{u} n)).obj (alphaObj n) ⟶[SSet.{u}]
    (rigidification.map (projection n)).obj (omegaObj n))
  have : WeakEquivalence p := (weakEquivalence_iff_GW _).2
    (DaggerActualCounitRightConeRelativeDirectedHomotopy.projection_hom_GW n)
  have hY : GW (toUnit Y) := by
    apply DaggerActualRigidificationSimplexHomContractibility.simplex_hom_toUnit_GW 1
    change Nonempty (Y.obj (op ⦋0⦌))
    dsimp [Y]
    rw [projection_alpha_obj, projection_omega_obj]
    exact ⟨edge⟩
  have : WeakEquivalence (toUnit Y) := (weakEquivalence_iff_GW _).2 hY
  have heq : p ≫ toUnit Y = toUnit (Q n) :=
    (SemiCartesianMonoidalCategory.isTerminalTensorUnit (C := SSet.{u})).hom_ext _ _
  apply (weakEquivalence_iff_GW _).1
  rw [← heq]
  infer_instance

/-- The original point-map convention gives the same unconditional Q[n] contractibility. -/
theorem Q_point_GW (n : ℕ) : GW (pointMap (Q.{u} n)) := by
  let e := pointIsTerminal.{u}.uniqueUpToIso
    (SemiCartesianMonoidalCategory.isTerminalTensorUnit (C := SSet.{u}))
  have : WeakEquivalence (toUnit (Q.{u} n)) := (weakEquivalence_iff_GW _).2 (Q_toUnit_GW n)
  have heq : toUnit (Q.{u} n) ≫ e.inv = pointMap (Q n) := pointIsTerminal.hom_ext _ _
  apply (weakEquivalence_iff_GW _).1
  rw [← heq]
  infer_instance

end
end DaggerActualCounitRightConeHomContractibility
