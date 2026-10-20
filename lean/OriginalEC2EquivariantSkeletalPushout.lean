import OriginalEC2EquivariantAttachingLegs
import Mathlib.CategoryTheory.Action.Limits

/-!
# The actual skeletal attaching pushout in the category of C₂ actions

All four maps have the previously checked literal underlying maps. Forgetful
colimit reflection and equivariant realization transport their pushout.
An exhaustive relative cell complex and model cofibrancy remain separate.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open DaggerOriginalDaggerRealizationC2Action DaggerOriginalEC2SimplicialAction
open DaggerOriginalEC2SkeletonAction DaggerOriginalEC2FreeCellAction
open DaggerOriginalEC2SkeletalPushout DaggerOriginalEC2OrdinaryRealizedPushout
open DaggerOriginalEC2EquivariantAttachingLegs

universe u

namespace DaggerOriginalEC2EquivariantSkeletalPushout

noncomputable section

/-- The boundary inclusion on the original regular cell coproduct actions. -/
def boundaryHom (n : ℕ) :
    freeCellAction (SSet.boundary n : SSet.{u}) ⟶ freeCellAction (Δ[n] : SSet.{u}) :=
  freeCellMap (SSet.boundary n).ι

/-- The original skeletal attachment is a pushout of actual C₂ actions. -/
theorem equivariantSkeletalPushout (n : ℕ) :
    IsPushout (attachingHom.{u} n) (boundaryHom.{u} n)
      (skeletonTransition.{u} n) (characteristicHom.{u} n) := by
  have h : IsPushout
      ((Action.forget SSet.{u} C2.{u}).map (attachingHom.{u} n))
      ((Action.forget SSet.{u} C2.{u}).map (boundaryHom.{u} n))
      ((Action.forget SSet.{u} C2.{u}).map (skeletonTransition.{u} n))
      ((Action.forget SSet.{u} C2.{u}).map (characteristicHom.{u} n)) :=
    ordinarySkeletalPushout.{u} n
  exact h.of_map_of_faithful (Action.forget SSet.{u} C2.{u})

/-- The original realization produces a pushout of topological C₂ actions. -/
theorem realizedEquivariantSkeletalPushout (n : ℕ) :
    IsPushout
      ((SSet.toTop.{u}.mapAction C2.{u}).map (attachingHom.{u} n))
      ((SSet.toTop.{u}.mapAction C2.{u}).map (boundaryHom.{u} n))
      ((SSet.toTop.{u}.mapAction C2.{u}).map (skeletonTransition.{u} n))
      ((SSet.toTop.{u}.mapAction C2.{u}).map (characteristicHom.{u} n)) :=
  (equivariantSkeletalPushout.{u} n).map (SSet.toTop.{u}.mapAction C2.{u})

end

end DaggerOriginalEC2EquivariantSkeletalPushout
