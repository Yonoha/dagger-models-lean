import ChallengeActualQRealizationQuillen
import ActualQRealizationQuillen
import ActualDaggerQuillenRightConeReduction

set_option autoImplicit false
universe u

namespace DaggerActualQRealizationQuillenChallenge

theorem verified : statement.{u} :=
  ⟨DaggerActualQRealizationQuillen.isQuillen,
    DaggerActualQRealizationHornWeakness.horn_trivialCofibration⟩

end DaggerActualQRealizationQuillenChallenge
