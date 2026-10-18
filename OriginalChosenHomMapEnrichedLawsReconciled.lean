import ChosenFlagOriginalHomNaturality

/-!
# Enriched identity and composition for the literal original chosen Hom map

These are the selected `C.map` enriched-functor laws with both source and
target `RV` endpoint transports. They do not replace the original Hom.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial EnrichedCategory MonoidalCategory
open DaggerModels.OrdinaryRigidification
open DaggerChosenRigidificationNecklace

universe u

namespace DaggerOriginalChosenHomMapEnrichedLaws

noncomputable section

variable {X Y : SSet.{u}} (f : X ⟶ Y)

/-- The original chosen map preserves the enriched identity. -/
theorem map_eId (a : X.obj (op ⦋0⦌)) :
    eId SSet (RV X a) ≫ originalChosenHomMap f a a =
      eId SSet (RV Y (f.app (op ⦋0⦌) a)) :=
  targetHomTransport_id (DaggerModels.OrdinaryRigidification.rigidification.map f)
    (RV X a) (RV Y (f.app (op ⦋0⦌) a))
    (RigidificationVertices.vertexEquiv_naturality f a)

/-- The original chosen map preserves the full enriched composition map. -/
theorem map_eComp (a b c : X.obj (op ⦋0⦌)) :
    eComp SSet (RV X a) (RV X b) (RV X c) ≫
        originalChosenHomMap f a c =
      (originalChosenHomMap f a b ⊗ₘ originalChosenHomMap f b c) ≫
        eComp SSet (RV Y (f.app (op ⦋0⦌) a))
          (RV Y (f.app (op ⦋0⦌) b))
          (RV Y (f.app (op ⦋0⦌) c)) :=
  targetHomTransport_comp
    (DaggerModels.OrdinaryRigidification.rigidification.map f)
    (RV X a) (RV X b) (RV X c)
    (RV Y (f.app (op ⦋0⦌) a))
    (RV Y (f.app (op ⦋0⦌) b))
    (RV Y (f.app (op ⦋0⦌) c))
    (RigidificationVertices.vertexEquiv_naturality f a)
    (RigidificationVertices.vertexEquiv_naturality f b)
    (RigidificationVertices.vertexEquiv_naturality f c)

end

end DaggerOriginalChosenHomMapEnrichedLaws
