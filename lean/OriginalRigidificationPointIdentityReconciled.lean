import OriginalRigidificationConstantArrowReconciled

/-!
# The zero-simplex identity maps to the original chosen identity

The point map is the actual Yoneda vertex. Both object transports are
retained before applying the existing enriched-functor identity law.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial EnrichedCategory MonoidalCategory
open DaggerModels.OrdinaryRigidification
open DaggerChosenRigidificationNecklace
open DaggerOriginalRigidificationZeroHom
open DaggerOriginalRigidificationConstantArrow

universe u

namespace DaggerOriginalRigidificationPointIdentity

noncomputable section

private abbrev Z : SSet.{u} := Δ[0]
private abbrev zeroObject :=
  RigidificationVertices.vertexEquiv Z.{u} vertex.{u}

/-- Evaluation of the actual Yoneda point map at the unique original vertex. -/
theorem pointMap_vertex (X : SSet.{u}) (a : X.obj (op ⦋0⦌)) :
    (pointMap X a).app (op ⦋0⦌) vertex.{u} = a := by
  change X.map (SimplexCategory.const ⦋0⦌ ⦋0⦌ 0).op a = a
  simp only [SimplexCategory.const_eq_id, op_id, FunctorToTypes.map_id_apply]

/-- The original Hom map of the point, with its second pair of endpoint casts. -/
def pointHom (X : SSet.{u}) (a : X.obj (op ⦋0⦌)) :
    (zeroObject.{u} ⟶[SSet.{u}] zeroObject.{u}) ⟶
      (RigidificationVertices.vertexEquiv X a ⟶[SSet.{u}]
        RigidificationVertices.vertexEquiv X a) :=
  originalChosenHomMap (pointMap X a) vertex.{u} vertex.{u} ≫
    targetHomTransport
      (congrArg (RigidificationVertices.vertexEquiv X) (pointMap_vertex X a))
      (congrArg (RigidificationVertices.vertexEquiv X) (pointMap_vertex X a))

/-- The map of a zero-simplex point sends its unique Hom arrow to `eId`. -/
theorem pointHom_identity (X : SSet.{u}) (a : X.obj (op ⦋0⦌)) :
    eId SSet zeroObject.{u} ≫ pointHom X a =
      eId SSet (RigidificationVertices.vertexEquiv X a) := by
  let h :=
    (RigidificationVertices.vertexEquiv_naturality (pointMap X a) vertex.{u}).trans
      (congrArg (RigidificationVertices.vertexEquiv X) (pointMap_vertex X a))
  calc
    eId SSet zeroObject.{u} ≫ pointHom X a =
        eId SSet zeroObject.{u} ≫
          (DaggerModels.OrdinaryRigidification.rigidification.map (pointMap X a)).map
            zeroObject.{u} zeroObject.{u} ≫ targetHomTransport h h := by
      simp only [pointHom, originalChosenHomMap, Category.assoc,
        targetHomTransport_trans]
    _ = eId SSet (RigidificationVertices.vertexEquiv X a) :=
      targetHomTransport_id
        (DaggerModels.OrdinaryRigidification.rigidification.map (pointMap X a))
        zeroObject.{u} (RigidificationVertices.vertexEquiv X a) h

end

end DaggerOriginalRigidificationPointIdentity
