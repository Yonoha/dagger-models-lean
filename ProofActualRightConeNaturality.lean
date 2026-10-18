import ChallengeActualRightConeNaturality
import ActualRightConeRigidificationNaturality
import ProofActualQQuillenEquivalence

set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial EnrichedCategory HomotopicalAlgebra
open DaggerModels DaggerModels.OrdinaryRigidification DaggerSSetGluing
universe u

namespace DaggerActualRightConeNaturalityChallenge

theorem verified : statement.{u} := by
  intro D hD
  refine ⟨fun v w ↦ DaggerActualRightConeKanMapping.rightCone_Kan D hD v w, ?_⟩
  intro E F hE
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v w
    change GW (DaggerActualRightConeFunctorialComparisons.postcomp F v w) ↔
      GW (DaggerActualRightConeFunctorialComparisons.homMap F v w)
    exact DaggerActualRightConeFunctorialComparisons.postcomp_GW_iff F v w hD hE
  · intro v w
    change DaggerOriginalCounitRightConeQRealizationAdjunction.realization.map
        (DaggerActualRightConeFunctorialComparisons.postcomp F v w) ≫
        DaggerOriginalCounitBNextConeRealizationFactorization.coneRigidificationMap E
          (DaggerActualRightConeFunctorialComparisons.vertexMap F v)
          (DaggerActualRightConeFunctorialComparisons.vertexMap F w) = _
    exact DaggerActualRightConeRigidificationNaturality.rigidification_naturality F v w
  · exact DaggerActualRightConeRigidificationNaturality.local_GW_iff F hD hE
  · intro v w n σ
    exact DaggerActualRightConeFunctorialComparisons.evaluation_postcomp F v w n σ

end DaggerActualRightConeNaturalityChallenge
