import ActualRigidificationSimplexHomContractibilityFormatted
import ActualEnrichedDirectedCylinder
import OriginalCounitRightConeRelativeHomotopyEndpoints
import OriginalEnrichedHomTransportRecovered

/-! Actual vertices and directed edges for the standard interval cylinder. -/

set_option autoImplicit false
open CategoryTheory EnrichedCategory MonoidalCategory CartesianMonoidalCategory
open Opposite Simplicial HomotopicalAlgebra
open DaggerModels.OrdinaryRigidification
open DaggerModels.OrdinaryRigidification.RigidificationVertices
open DaggerChosenRigidificationNecklace hiding thickeningUnit
open DaggerOrdinaryPiZeroCategory DaggerOrdinaryTranslation DaggerSSetGluing
open DaggerOriginalCounitRightConeRelativeHomotopy
open scoped SSet.modelCategoryQuillen
universe u

namespace DaggerActualRigidificationDirectedIntervalObjects

noncomputable section

def endpoint (t : Fin 2) : (rigidification.obj (Δ[1] : SSet.{u})).Obj :=
  vertexEquiv Δ[1] (SSet.stdSimplex.obj₀Equiv.symm t)

theorem thickening_endpoint (t : Fin 2) :
    (thickeningUnit.app ⦋1⦌).obj ⟨ULift.up t⟩ = endpoint.{u} t := by
  symm
  rw [endpoint, vertexEquiv_apply]
  exact canonicalVertex_simplex ⦋1⦌ (SSet.stdSimplex.obj₀Equiv.symm t)

/-- The forward edge is the image of the actual two-element thickening path. -/
def edge : (endpoint.{u} 0 ⟶[SSet.{u}] endpoint.{u} 1).obj (op ⦋0⦌) :=
  (((thickeningUnit.app ⦋1⦌).map ⟨ULift.up (0 : Fin 2)⟩ ⟨ULift.up (1 : Fin 2)⟩) ≫
    targetHomTransport (thickening_endpoint 0) (thickening_endpoint 1)).app (op ⦋0⦌)
      ((Functor.const _).obj
        (DaggerActualThickeningPathContractibility.shortestPath
          (ULift.up (0 : Fin 2)) (ULift.up (1 : Fin 2)) (by decide)))

instance point_objects_subsingleton :
    Subsingleton (rigidification.obj (Δ[0] : SSet.{u})).Obj := by
  constructor
  intro a b
  apply (vertexEquiv Δ[0]).symm.injective
  apply SSet.stdSimplex.obj₀Equiv.injective
  apply Fin.ext
  omega

/-- Every endomorphism component of the actual rigidification of the point is trivial. -/
instance point_hom_piZero_subsingleton
    (a : (rigidification.obj (Δ[0] : SSet.{u})).Obj) :
    Subsingleton (SSet.π₀ (a ⟶[SSet.{u}] a)) := by
  have : WeakEquivalence (toUnit (a ⟶[SSet.{u}] a)) :=
    (weakEquivalence_iff_GW _).2
      (DaggerActualRigidificationSimplexHomContractibility.simplex_hom_toUnit_GW
        0 a a ⟨idVertex (rigidification.obj Δ[0]) a⟩)
  constructor
  intro x y
  apply (DaggerUnitaryInterval.bijective_mapPiZero
    (toUnit (a ⟶[SSet.{u}] a)) inferInstance).1
  obtain ⟨x, rfl⟩ := SSet.π₀.mk_surjective x
  obtain ⟨y, rfl⟩ := SSet.π₀.mk_surjective y
  apply congrArg SSet.π₀.mk
  exact Subsingleton.elim (α := PUnit.{u + 1}) _ _

/-- Every supplied point-Hom vertex is invertible in the original component category. -/
theorem point_vertex_class_isIso
    {a b : (rigidification.obj (Δ[0] : SSet.{u})).Obj}
    (v : (a ⟶[SSet.{u}] b).obj (op ⦋0⦌)) :
    IsIso (classOfVertex (rigidification.obj Δ[0]) v) := by
  have h : a = b := Subsingleton.elim _ _
  cases h
  have hclass : classOfVertex (rigidification.obj Δ[0]) v =
      𝟙 (show hC (rigidification.obj Δ[0]) from a) :=
    @Subsingleton.elim (SSet.π₀ (a ⟶[SSet.{u}] a))
      (point_hom_piZero_subsingleton a) _ _
  rw [hclass]
  infer_instance

/-- The literal vertical line through an original rigidification object. -/
def vertexLine (X : SSet.{u}) (a : (rigidification.obj X).Obj) : Δ[1] ⟶ X ⊗ Δ[1] :=
  CartesianMonoidalCategory.lift (SSet.const ((vertexEquiv X).symm a)) (𝟙 Δ[1])

theorem vertexLine_endpoint (X : SSet.{u}) (a : (rigidification.obj X).Obj) (t : Fin 2) :
    (rigidification.map (vertexLine X a)).obj (endpoint t) =
      (rigidification.map (timeSlice X t)).obj a := by
  calc
    _ = vertexEquiv (X ⊗ Δ[1])
        ((vertexLine X a).app (op ⦋0⦌) (SSet.stdSimplex.obj₀Equiv.symm t)) :=
      vertexEquiv_naturality _ _
    _ = vertexEquiv (X ⊗ Δ[1])
        ((timeSlice X t).app (op ⦋0⦌) ((vertexEquiv X).symm a)) := by
      apply congrArg (vertexEquiv (X ⊗ Δ[1]))
      change (X.map (SimplexCategory.const ⦋0⦌ ⦋0⦌ 0).op
        ((vertexEquiv X).symm a), SSet.stdSimplex.obj₀Equiv.symm t) =
        ((vertexEquiv X).symm a, SSet.stdSimplex.const 1 t (op ⦋0⦌))
      simp only [SimplexCategory.const_eq_id, op_id, FunctorToTypes.map_id_apply]
      rfl
    _ = (rigidification.map (timeSlice X t)).obj
        (vertexEquiv X ((vertexEquiv X).symm a)) := (vertexEquiv_naturality _ _).symm
    _ = (rigidification.map (timeSlice X t)).obj a :=
      congrArg (rigidification.map (timeSlice X t)).obj ((vertexEquiv X).apply_symm_apply a)

/-- Both endpoints are transported to the actual time-slice objects. -/
def verticalEdge (X : SSet.{u}) (a : (rigidification.obj X).Obj) :
    ((rigidification.map (timeSlice X 0)).obj a ⟶[SSet.{u}]
      (rigidification.map (timeSlice X 1)).obj a).obj (op ⦋0⦌) :=
  ((rigidification.map (vertexLine X a)).map (endpoint 0) (endpoint 1) ≫
    targetHomTransport (vertexLine_endpoint X a 0) (vertexLine_endpoint X a 1)).app
      (op ⦋0⦌) edge

end
end DaggerActualRigidificationDirectedIntervalObjects
