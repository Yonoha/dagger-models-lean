import ChallengeActualFibrantRightConeEndpoints
import ProofActualFibrantOrdinalGadgets
import ActualFibrantRightConeEndpoints

/-! Verify unconditional endpoint contractibility in the full saved model-category context. -/
set_option autoImplicit false
universe u
namespace DaggerActualFibrantRightConeEndpointsProof

theorem verified : DaggerActualFibrantRightConeEndpointsChallenge.statement.{u} :=
  DaggerActualFibrantRightConeEndpoints.endpoint_hom_toUnit_GW

end DaggerActualFibrantRightConeEndpointsProof
