import ChallengeNativeStructuredArrowChainBijection
import ChallengeActualConeIndexWeakness
import ActualIteratedConeIndexWeakness

/-! The exact independent statements follow without an additional weak-comparison premise. -/
set_option autoImplicit false
universe u
namespace DaggerActualConeIndexWeaknessProof

theorem chain_bijection_verified :
    DaggerNativeStructuredArrowChainBijectionChallenge.statement.{u} := by
  intro C D _ _ F d n
  exact (DaggerNativeStructuredArrowChainDecomposition.chainEquiv F d n).bijective

theorem verified : DaggerActualConeIndexWeaknessChallenge.statement.{u} := by
  refine ⟨?_, ?_, ?_⟩
  · intro C D _ _ F hF
    exact DaggerNativeDualTheoremA.nerveMap_GW F hF
  · exact DaggerActualIteratedFirstConeProjectionWeakness.first_projection_GW
  · exact DaggerActualIteratedConeIndexWeakness.index_GW

end DaggerActualConeIndexWeaknessProof
