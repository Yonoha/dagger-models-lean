import ChallengeActualNecklaceConeBridge
import ActualNecklaceConeP2Span
import ProofActualRightConeNaturality

/-! Verify the common-gadget statement in the existing full dagger-model/Q context. -/
set_option autoImplicit false
universe u
namespace DaggerActualNecklaceConeBridgeProof

theorem verified : DaggerActualNecklaceConeBridgeChallenge.statement.{u} := by
  refine ⟨?_, ?_, ?_⟩
  · intro X a b
    exact ⟨DaggerActualNecklaceConeGadgetComparison.inclusion_GW X a b,
      DaggerActualNecklaceConeGadgetComparison.comma_point_GW,
      DaggerActualNecklaceConeP2Span.toOriginalHom_GW X a b,
      DaggerActualNecklaceConeP2Span.toGadgets_GW X a b⟩
  · exact DaggerActualRightConeGadgetIndex.index_obj_map
  · intro D v w σ τ f
    exact DaggerActualRightConeGadgetIndex.index_map_original D v w f

end DaggerActualNecklaceConeBridgeProof
