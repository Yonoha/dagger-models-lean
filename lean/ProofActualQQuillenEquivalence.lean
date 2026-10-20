import ChallengeActualQQuillenEquivalence
import ActualQQuillenEquivalence
import ActualRightConeEvaluationWeak
import ProofActualQDerivedCounit

set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen
universe u

namespace DaggerActualQQuillenEquivalenceChallenge

theorem verified : statement.{u} := by
  refine ⟨fun X Y f ↦ DaggerActualQRealizationWeakReflection.realization_GW_iff f, ?_,
    DaggerActualQQuillenEquivalence.isQuillenEquivalence, ?_⟩
  · intro X hX
    have : X.KanComplex := hX
    exact DaggerActualQKanCounitWeakEquivalence.counit_GW X
  · exact DaggerActualRightConeEvaluationWeak.evaluation_GW

end DaggerActualQQuillenEquivalenceChallenge
