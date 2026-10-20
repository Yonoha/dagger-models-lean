import OriginalRigidificationZeroHomIdentityReconciled
import OriginalChosenHomMapFunctorialityReconciled
import OriginalCounitRightConeCrossTimeSectionsReconciled

/-!
# Factoring a constant original arrow through the actual zero-simplex

The first-coordinate projection of a vertical line is a constant map.
Its directed enriched arrow factors through the actual original Hom of
`C Δ[0]`, where the whole Hom map is uniquely the identity arrow.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial EnrichedCategory MonoidalCategory
open CartesianMonoidalCategory
open DaggerModels.OrdinaryRigidification
open DaggerChosenRigidificationNecklace
open DaggerModels.OrdinaryRigidification.DirectedIntervalHom
open DaggerOriginalRigidificationZeroHom
open DaggerOriginalRigidificationZeroHomIdentity
open DaggerOriginalCounitRightConeCrossTimeSections

universe u

namespace DaggerOriginalRigidificationConstantArrow

noncomputable section

private abbrev I : SSet.{u} := Δ[1]
private abbrev Z : SSet.{u} := Δ[0]

/-- Collapse the directed interval onto the actual zero-simplex vertex. -/
def collapse : I.{u} ⟶ Z.{u} := SSet.const vertex.{u}

/-- The actual map represented by one vertex of X. -/
def pointMap (X : SSet.{u}) (a : X.obj (op ⦋0⦌)) : Z.{u} ⟶ X :=
  SSet.yonedaEquiv.symm a

/-- The literal constant map factors through the zero-simplex. -/
theorem constant_factor (X : SSet.{u}) (a : X.obj (op ⦋0⦌)) :
    collapse.{u} ≫ pointMap X a = SSet.const (X := I.{u}) a := by
  rw [collapse, SSet.const_comp]
  congr 1
  change X.map (SimplexCategory.const ⦋0⦌ ⦋0⦌ 0).op a = a
  simp only [SimplexCategory.const_eq_id, op_id, FunctorToTypes.map_id_apply]

/-- The first directed endpoint collapses to the only zero-simplex vertex. -/
theorem collapse_zero :
    collapse.{u}.app (op ⦋0⦌) vertexZero.{u} = vertex.{u} := by
  change Z.{u}.map (SimplexCategory.const ⦋0⦌ ⦋0⦌ 0).op vertex.{u} = vertex.{u}
  simp only [SimplexCategory.const_eq_id, op_id, FunctorToTypes.map_id_apply]

/-- The second directed endpoint collapses to the same original vertex. -/
theorem collapse_one :
    collapse.{u}.app (op ⦋0⦌) vertexOne.{u} = vertex.{u} := by
  change Z.{u}.map (SimplexCategory.const ⦋0⦌ ⦋0⦌ 0).op vertex.{u} = vertex.{u}
  simp only [SimplexCategory.const_eq_id, op_id, FunctorToTypes.map_id_apply]

/-- The actual original Hom map of the collapse, with both endpoint casts. -/
def collapseHom :
    DaggerOriginalRigidificationDirectedProductProjection.intervalHom.{u} ⟶
      (RigidificationVertices.vertexEquiv Z.{u} vertex.{u} ⟶[SSet.{u}]
        RigidificationVertices.vertexEquiv Z.{u} vertex.{u}) :=
  originalChosenHomMap collapse.{u} vertexZero.{u} vertexOne.{u} ≫
    targetHomTransport
      (congrArg (RigidificationVertices.vertexEquiv Z.{u}) collapse_zero.{u})
      (congrArg (RigidificationVertices.vertexEquiv Z.{u}) collapse_one.{u})

/-- Collapsing the directed arrow gives the zero-simplex enriched identity. -/
theorem collapse_directed_identity :
    directedArrow.{u} ≫ collapseHom.{u} =
      toUnit (𝟙_ SSet.{u}) ≫
        eId SSet (RigidificationVertices.vertexEquiv Z.{u} vertex.{u}) :=
  to_identity (𝟙_ SSet.{u}) (directedArrow.{u} ≫ collapseHom.{u})

end

end DaggerOriginalRigidificationConstantArrow
