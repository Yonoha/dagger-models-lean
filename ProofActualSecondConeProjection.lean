import ChallengeNativeSmallHomNerveLift
import ChallengeActualSecondConeProjection
import ActualIteratedSecondConeProjection

set_option autoImplicit false
open CategoryTheory
universe u
namespace DaggerActualSecondConeProjectionProof
noncomputable section

theorem nerveLift_verified : DaggerNativeSmallHomNerveLiftChallenge.statement.{u} := by
  intro C inst
  exact ⟨DaggerNativeSmallHomNerveLift.iso C, fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩

theorem verified : DaggerActualSecondConeProjectionChallenge.statement.{u} := by
  constructor
  · intro D a b P k σ ha hb
    refine ⟨DaggerActualIteratedSecondConeProjection.toMapping D a b P k σ ha hb,
      fun _ ↦ rfl, ?_, fun _ _ _ ↦ HEq.rfl, ?_⟩
    · intro A
      exact heq_of_eq (DaggerActualIteratedSecondConeProjection.toMapping_wholeMap
        D a b P k σ ha hb A)
    · exact DaggerActualIteratedSecondConeProjection.toMapping_GW D a b P k σ ha hb
  · exact DaggerActualIteratedSecondConeProjection.all_positive_comparisons

end
end DaggerActualSecondConeProjectionProof
