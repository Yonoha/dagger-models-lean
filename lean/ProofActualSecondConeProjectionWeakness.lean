import ChallengeNativeSimplexColumnBijection
import ChallengeActualSecondConeProjectionWeakness
import ActualIteratedSecondConeProjectionWeakness

/-! Proofs of the independent original statements, without supplying their conclusions as inputs. -/
set_option autoImplicit false
universe u
namespace DaggerActualSecondConeProjectionWeaknessProof

theorem column_bijection_verified : DaggerNativeSimplexColumnBijectionChallenge.statement.{u} := by
  intro X q k
  exact (DaggerNativeSimplexIndexResolutionColumnComparison.columnEquiv X q k).bijective

theorem verified : DaggerActualSecondConeProjectionWeaknessChallenge.statement.{u} := by
  refine ⟨?_, ?_, ?_⟩
  · exact DaggerNativeSimplexIndexNerveWeakContractibility.index_toUnit_GW
  · exact DaggerActualIteratedSecondConeProjectionWeakness.comma_point_GW
  · exact DaggerActualIteratedSecondConeProjectionWeakness.second_projection_GW

end DaggerActualSecondConeProjectionWeaknessProof
