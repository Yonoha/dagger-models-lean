import ChallengeActualIteratedFibrantStructuredArrows
import ActualIteratedFibrantStructuredArrows
import ProofActualIteratedFibrantGadgets

/-! Verify the literal structured-arrow claim in the same full original model context. -/
set_option autoImplicit false
universe u
namespace DaggerActualIteratedFibrantStructuredArrowsProof

theorem verified : DaggerActualIteratedFibrantStructuredArrowsChallenge.statement.{u} :=
  DaggerActualIteratedFibrantStructuredArrows.toUnit_GW

end DaggerActualIteratedFibrantStructuredArrowsProof
