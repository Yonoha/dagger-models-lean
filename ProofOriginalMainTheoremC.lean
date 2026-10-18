import ChallengeOriginalMainTheoremC
import NativeOriginalMainCRecognition

/-! Proof of the unchanged FROZEN FULL original Main Theorem C. -/
set_option autoImplicit false
universe u
namespace DaggerProofOriginalMainTheoremC

theorem verified : DaggerChallengeOriginalMainTheoremC.Statement.{u} :=
  DaggerNativeOriginalMainCRecognition.verified

end DaggerProofOriginalMainTheoremC
