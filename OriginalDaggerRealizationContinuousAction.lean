import OriginalDaggerRealizationC2Action
import Mathlib.CategoryTheory.Action.Continuous
import Mathlib.Topology.ContinuousOn

/-!
# The original realized dagger as a continuous action

The actual two-element group is given its discrete topology. Joint continuity
uses Mathlib's discrete-product criterion and the existing continuous maps.
No EC₂ model or homotopy-fixed-point recognition is asserted.
-/

set_option autoImplicit false

open CategoryTheory DaggerModels Opposite Simplicial
open DaggerOriginalDaggerRealizationC2Action
open DaggerOriginalDaggerRealizationInvolution
open DaggerOriginalDaggerRealizationVertices

universe u

namespace DaggerOriginalDaggerRealizationContinuousAction

noncomputable section

/-- Regard a topological space as itself through the identity forgetful functor. -/
instance topCatSelfForget : HasForget₂ TopCat.{u} TopCat.{u} where
  forget₂ := 𝟭 _
  forget_comp := Functor.id_comp _

/-- The finite acting group carries the discrete topology. -/
instance c2Topology : TopologicalSpace C2.{u} := ⊥

/-- This topology is literally discrete, in every universe. -/
instance c2DiscreteTopology : DiscreteTopology C2.{u} := ⟨rfl⟩

/-- The original action is jointly continuous in the group element and point. -/
theorem realizedAction_isContinuous (X : DaggerSSet.{u}) :
    (realizedAction X).IsContinuous := by
  rw [Action.isContinuous_def]
  apply continuous_prod_of_discrete_left.mpr
  intro g
  change Continuous (fun x : SSet.toTop.obj X.toSSet ↦ (actionEnd X g).asHom x)
  exact (actionEnd X g).asHom.hom.continuous

/-- Lift the same realization functor to Mathlib's continuous-action category. -/
def realizedContinuousActionFunctor : DaggerSSet.{u} ⥤ ContAction TopCat.{u} C2.{u} :=
  ObjectProperty.lift _ realizedActionFunctor realizedAction_isContinuous

/-- The underlying object is the original geometric realization. -/
theorem realizedContinuousActionFunctor_obj (X : DaggerSSet.{u}) :
    (realizedContinuousActionFunctor.obj X).obj.V = SSet.toTop.obj X.toSSet := rfl

/-- The underlying morphism is the original realized dagger morphism. -/
theorem realizedContinuousActionFunctor_map {X Y : DaggerSSet.{u}} (f : X ⟶ Y) :
    (realizedContinuousActionFunctor.map f).hom.hom = SSet.toTop.map f.hom := rfl

/-- The generator acts by the literal previously proved involution. -/
theorem realizedContinuousActionFunctor_generator (X : DaggerSSet.{u}) :
    (realizedContinuousActionFunctor.obj X).obj.ρ generator =
      realizationInvolutionHom X :=
  realizedAction_generator X

/-- Every original realized vertex remains fixed by the continuous action. -/
theorem realizedContinuousVertex_fixed (X : DaggerSSet.{u})
    (x : X.toSSet _⦋0⦌) (g : C2.{u}) :
    ((realizedContinuousActionFunctor.obj X).obj.ρ g).asHom
      (realizedVertex X x) = realizedVertex X x :=
  realizedVertex_action_fixed X x g

end

end DaggerOriginalDaggerRealizationContinuousAction
