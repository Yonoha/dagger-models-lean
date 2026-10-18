import ChallengeAdjunctionLiftingTransfer

set_option autoImplicit false
open CategoryTheory
universe u v u' v'
namespace DaggerOriginalAdjunctionLiftingTransferChallengeProof

/-- Reuse the native lifting-property equivalence of an adjunction without a model structure. -/
theorem challengeProof : ChallengeAdjunctionLiftingTransfer.Statement.{u, v, u', v'} := by
  intro C _ D _ F G adj P Q h A B i hi X Y p hp
  exact (adj.hasLiftingProperty_iff i p).2 (hi _ (h p hp))

end DaggerOriginalAdjunctionLiftingTransferChallengeProof
