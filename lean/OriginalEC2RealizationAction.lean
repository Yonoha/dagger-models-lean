import OriginalEC2SimplicialAction
import OriginalDaggerRealizationContinuousAction
import OriginalEquivariantConstantMaps

/-!
# The actual realized EC₂ as a continuous C₂-action

The object is the realization of the literal nerve of the codiscrete C₂.
Only continuity of its action is asserted here; topological freeness is separate.
-/

set_option autoImplicit false

open CategoryTheory DaggerModels Opposite Simplicial
open DaggerOriginalDaggerRealizationC2Action
open DaggerOriginalDaggerRealizationContinuousAction
open DaggerOriginalEC2SimplicialAction

universe u

namespace DaggerOriginalEC2RealizationAction

noncomputable section

/-- Realize the original simplicial action, without changing its underlying nerve. -/
def realizedEC2Action : Action TopCat.{u} C2.{u} :=
  (SSet.toTop.{u}.mapAction C2.{u}).obj simplicialAction.{u}

/-- The underlying space is the actual realization of the codiscrete nerve. -/
theorem realizedEC2Action_obj :
    realizedEC2Action.{u}.V = SSet.toTop.obj simplicialEC2.{u} := rfl

/-- Each action endomorphism is the realization of the original simplicial one. -/
theorem realizedEC2Action_map (g : C2.{u}) :
    (realizedEC2Action.{u}.ρ g).asHom =
      SSet.toTop.map ((simplicialAction.{u}.ρ g).asHom) := rfl

/-- The realized action is jointly continuous for the actual discrete C₂. -/
theorem realizedEC2Action_isContinuous : realizedEC2Action.{u}.IsContinuous := by
  rw [Action.isContinuous_def]
  apply continuous_prod_of_discrete_left.mpr
  intro g
  change Continuous (fun x : SSet.toTop.obj simplicialEC2.{u} ↦
    (realizedEC2Action.{u}.ρ g).asHom x)
  exact ((realizedEC2Action.{u}.ρ g).asHom).hom.continuous

/-- The actual EC₂ realization in Mathlib's continuous-action category. -/
def realizedEC2ContinuousAction : ContAction TopCat.{u} C2.{u} :=
  ⟨realizedEC2Action.{u}, realizedEC2Action_isContinuous.{u}⟩

/-- Its underlying space is still the original realized codiscrete nerve. -/
theorem realizedEC2ContinuousAction_obj :
    realizedEC2ContinuousAction.{u}.obj.V =
      SSet.toTop.obj simplicialEC2.{u} := rfl

/-- Specialize the established equivariant constant-map construction to actual EC₂. -/
def canonicalConstantMap (X : DaggerSSet.{u}) (x : X.toSSet _⦋0⦌) :
    DaggerOriginalEquivariantConstantMaps.EquivariantMaps
      realizedEC2ContinuousAction.{u}
      (realizedContinuousActionFunctor.obj X) :=
  DaggerOriginalEquivariantConstantMaps.canonicalConstantMap
    realizedEC2ContinuousAction.{u} X x

/-- This specialized map has the original realized vertex as its literal value. -/
theorem canonicalConstantMap_apply (X : DaggerSSet.{u})
    (x : X.toSSet _⦋0⦌) (e : realizedEC2ContinuousAction.{u}.obj.V) :
    (canonicalConstantMap X x).val e =
      DaggerOriginalDaggerRealizationVertices.realizedVertex X x :=
  DaggerOriginalEquivariantConstantMaps.canonicalConstantMap_apply
    realizedEC2ContinuousAction.{u} X x e

end

end DaggerOriginalEC2RealizationAction
