import ChallengeActualRightConeSingularComparison
import ActualRightConeEvaluationCounitReduction
import ProofActualQRealizationWeakEquivalences

set_option autoImplicit false
universe u

namespace DaggerActualRightConeSingularComparisonChallenge

theorem verified : statement.{u} :=
  ⟨fun n ↦ ⟨DaggerActualRightConeTwoObjectCellIso.cellIso n⟩,
    fun D v w ↦ DaggerActualRightConeSingularComparisonIso.comparison_isIso D v w⟩

end DaggerActualRightConeSingularComparisonChallenge
