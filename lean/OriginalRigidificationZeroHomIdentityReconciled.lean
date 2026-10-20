import OriginalRigidificationZeroHomReconciled

/-!
# Every arrow to the original zero-simplex Hom is an identity arrow

This is an equality of whole simplicial-set maps. It will be applied to the
image of the directed interval arrow under collapse to `Δ[0]`.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial EnrichedCategory MonoidalCategory
open CartesianMonoidalCategory
open DaggerModels.OrdinaryRigidification
open DaggerOriginalRigidificationZeroHom

universe u

namespace DaggerOriginalRigidificationZeroHomIdentity

noncomputable section

private abbrev zeroObject :=
  RigidificationVertices.vertexEquiv (Δ[0] : SSet.{u}) vertex.{u}

/-- The identity arrow is the unique map into the original zero-simplex Hom. -/
theorem to_identity (Z : SSet.{u})
    (f : Z ⟶ (zeroObject.{u} ⟶[SSet.{u}] zeroObject.{u})) :
    f = toUnit Z ≫ eId SSet zeroObject.{u} :=
  originalHomIsTerminal.{u}.hom_ext _ _

end

end DaggerOriginalRigidificationZeroHomIdentity
