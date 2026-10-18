import OriginalDiscreteCoherentUnitaryObstructionReconciled
import OriginalWalkingIsoIntegerObstruction

set_option autoImplicit false

open CategoryTheory HomotopicalAlgebra Simplicial DaggerModels
open DaggerUnitaryDiscrete DaggerUnitaryInvariance

universe u

namespace DaggerModels.OriginalWalkingIsoCoherentObstruction

open OriginalWalkingIsoIntegerObstruction
open OriginalDiscreteCoherentUnitaryObstruction

/-- No coherent-unitary class connects the lifted integer target's original two endpoints. -/
theorem integerTarget_noCoherentUnitary (R : FunctorialFibrantReplacement.{u})
    (z : SSet.π₀
      ((ordinaryEnrichment integerTarget.{u}).enriched.Hom
        integerZero integerOne)) :
    ¬ CoherentlyUnitary R (ordinaryEnrichment integerTarget.{u})
      integerZero integerOne z :=
  noCoherentUnitaryOfNoUnitary integerTarget.{u} R integerZero integerOne
    (fun f ↦ integer_noUnitary f) z

end DaggerModels.OriginalWalkingIsoCoherentObstruction
