import ChallengeActualQRealizationWeakEquivalences
import ActualQRealizationWeakEquivalences
import ProofActualQRealizationQuillen

set_option autoImplicit false
universe u

namespace DaggerActualQRealizationWeakEquivalencesChallenge

theorem verified : statement.{u} := by
  intro X Y f hf
  exact DaggerActualQRealizationWeakEquivalences.realization_GW f hf

end DaggerActualQRealizationWeakEquivalencesChallenge
