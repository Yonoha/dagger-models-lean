import ChallengeActualFibrantOrdinalGadgets
import ProofActualFibrantSimplex
import ActualFibrantRightConeContractibility

/-! Verify the entire original-map challenge in the saved full model-category context. -/
set_option autoImplicit false
universe u
namespace DaggerActualFibrantOrdinalGadgetsProof

theorem verified : DaggerActualFibrantOrdinalGadgetsChallenge.statement.{u} := by
  obtain ⟨hthin, hfib, hsimplex⟩ := DaggerActualFibrantSimplexProof.verified.{u}
  exact ⟨hthin, hfib, hsimplex,
    DaggerActualFibrantRightConeContractibility.cone_gadget_hom_toUnit_GW⟩

end DaggerActualFibrantOrdinalGadgetsProof
