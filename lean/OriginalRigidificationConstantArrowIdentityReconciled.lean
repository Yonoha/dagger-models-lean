import OriginalRigidificationPointIdentityReconciled

/-!
# The actual constant original Hom map sends the directed arrow to identity

The map is factored through `C Δ[0]`. Both original endpoint equalities are
retained, even when the original map identifies the two directed vertices.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial EnrichedCategory MonoidalCategory
open CartesianMonoidalCategory
open DaggerModels.OrdinaryRigidification
open DaggerChosenRigidificationNecklace
open DaggerModels.OrdinaryRigidification.DirectedIntervalHom
open DaggerOriginalRigidificationConstantArrow
open DaggerOriginalRigidificationPointIdentity
open DaggerOriginalCounitRightConeCrossTimeSections

universe u

namespace DaggerOriginalRigidificationConstantArrowIdentity

noncomputable section

private abbrev I : SSet.{u} := Δ[1]

/-- The constant map sends the first actual directed endpoint to `a`. -/
theorem const_zero (X : SSet.{u}) (a : X.obj (op ⦋0⦌)) :
    (SSet.const (X := I.{u}) a).app (op ⦋0⦌) vertexZero.{u} = a := by
  change X.map (SimplexCategory.const ⦋0⦌ ⦋0⦌ 0).op a = a
  simp only [SimplexCategory.const_eq_id, op_id, FunctorToTypes.map_id_apply]

/-- The constant map sends the second actual directed endpoint to `a`. -/
theorem const_one (X : SSet.{u}) (a : X.obj (op ⦋0⦌)) :
    (SSet.const (X := I.{u}) a).app (op ⦋0⦌) vertexOne.{u} = a := by
  change X.map (SimplexCategory.const ⦋0⦌ ⦋0⦌ 0).op a = a
  simp only [SimplexCategory.const_eq_id, op_id, FunctorToTypes.map_id_apply]

/-- The full original Hom map of a constant simplicial map, with both casts. -/
def constantHom (X : SSet.{u}) (a : X.obj (op ⦋0⦌)) :
    DaggerOriginalRigidificationDirectedProductProjection.intervalHom.{u} ⟶
      (RigidificationVertices.vertexEquiv X a ⟶[SSet.{u}]
        RigidificationVertices.vertexEquiv X a) :=
  originalChosenHomMap (SSet.const (X := I.{u}) a)
      vertexZero.{u} vertexOne.{u} ≫
    targetHomTransport
      (congrArg (RigidificationVertices.vertexEquiv X) (const_zero X a))
      (congrArg (RigidificationVertices.vertexEquiv X) (const_one X a))

/-- The full constant Hom map is the zero-simplex collapse then the point Hom. -/
theorem constantHom_factor (X : SSet.{u}) (a : X.obj (op ⦋0⦌)) :
    constantHom X a = collapseHom.{u} ≫ pointHom X a := by
  have comp_transport (Y : SSet.{u}) (f : I.{u} ⟶ Y) (g : Y ⟶ X)
      (b0 b1 : Y.obj (op ⦋0⦌))
      (hf0 : f.app (op ⦋0⦌) vertexZero.{u} = b0)
      (hf1 : f.app (op ⦋0⦌) vertexOne.{u} = b1)
      (hg0 : g.app (op ⦋0⦌) b0 = a)
      (hg1 : g.app (op ⦋0⦌) b1 = a)
      (hfg0 : (f ≫ g).app (op ⦋0⦌) vertexZero.{u} = a)
      (hfg1 : (f ≫ g).app (op ⦋0⦌) vertexOne.{u} = a) :
      originalChosenHomMap (f ≫ g) vertexZero.{u} vertexOne.{u} ≫
          targetHomTransport (congrArg (RV X) hfg0) (congrArg (RV X) hfg1) =
        (originalChosenHomMap f vertexZero.{u} vertexOne.{u} ≫
          targetHomTransport (congrArg (RV Y) hf0) (congrArg (RV Y) hf1)) ≫
        (originalChosenHomMap g b0 b1 ≫
          targetHomTransport (congrArg (RV X) hg0) (congrArg (RV X) hg1)) := by
    cases hf0
    cases hf1
    rw [DaggerOriginalChosenHomMapFunctoriality.originalChosenHomMap_comp]
    simp only [SSet.comp_app, types_comp_apply, targetHomTransport, eqToHom_refl,
      Category.comp_id, Category.assoc]
  have congr_map (f g : I.{u} ⟶ X) (hfg : f = g)
      (hf0 : f.app (op ⦋0⦌) vertexZero.{u} = a)
      (hf1 : f.app (op ⦋0⦌) vertexOne.{u} = a)
      (hg0 : g.app (op ⦋0⦌) vertexZero.{u} = a)
      (hg1 : g.app (op ⦋0⦌) vertexOne.{u} = a) :
      originalChosenHomMap f vertexZero.{u} vertexOne.{u} ≫
          targetHomTransport (congrArg (RV X) hf0) (congrArg (RV X) hf1) =
        originalChosenHomMap g vertexZero.{u} vertexOne.{u} ≫
          targetHomTransport (congrArg (RV X) hg0) (congrArg (RV X) hg1) := by
    cases hfg
    rfl
  have h0 : (collapse.{u} ≫ pointMap X a).app (op ⦋0⦌) vertexZero.{u} = a := by
    simp only [SSet.comp_app, types_comp_apply, collapse_zero, pointMap_vertex]
  have h1 : (collapse.{u} ≫ pointMap X a).app (op ⦋0⦌) vertexOne.{u} = a := by
    simp only [SSet.comp_app, types_comp_apply, collapse_one, pointMap_vertex]
  calc
    constantHom X a =
        originalChosenHomMap (collapse.{u} ≫ pointMap X a) vertexZero.{u} vertexOne.{u} ≫
          targetHomTransport (congrArg (RV X) h0) (congrArg (RV X) h1) :=
      congr_map _ _ (constant_factor X a).symm (const_zero X a) (const_one X a) h0 h1
    _ = collapseHom.{u} ≫ pointHom X a := by
      unfold collapseHom pointHom
      exact comp_transport _ _ _ DaggerOriginalRigidificationZeroHom.vertex.{u}
        DaggerOriginalRigidificationZeroHom.vertex.{u} collapse_zero collapse_one
        (pointMap_vertex X a) (pointMap_vertex X a) h0 h1

/-- Every directed arrow maps to the original enriched identity under a constant map. -/
theorem directed_constant_identity (X : SSet.{u}) (a : X.obj (op ⦋0⦌)) :
    directedArrow.{u} ≫ constantHom X a =
      eId SSet (RigidificationVertices.vertexEquiv X a) := by
  rw [constantHom_factor, ← Category.assoc, collapse_directed_identity]
  rw [Category.assoc, pointHom_identity]
  have hunit : toUnit (𝟙_ SSet.{u}) = 𝟙 (𝟙_ SSet.{u}) :=
    isTerminalTensorUnit.hom_ext _ _
  rw [hunit, Category.id_comp]

end

end DaggerOriginalRigidificationConstantArrowIdentity
