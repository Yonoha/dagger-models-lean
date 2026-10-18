import ChallengeActualDaggerModelMain
import ProofActualDaggerModel
import ProofActualDaggerLeftProper

set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra DaggerModels
universe u

namespace DaggerActualModelMainChallenge

theorem verified : statement.{u} := by
  refine ⟨DaggerOriginalJoyalModel.standardModelCategory, ?_,
    DaggerActualModelChallenge.generationVerified,
    DaggerActualLeftProperChallenge.leftProperVerified, ?_⟩
  · exact ⟨DaggerOriginalJoyalModel.standard_model_weak,
      DaggerOriginalJoyalModel.standard_model_cof, DaggerOriginalJoyalModel.standard_model_fib⟩
  · intro X Y p
    exact DaggerOriginalJoyalModel.trivialFibration_iff_ordinary_trivial
      DaggerUnitaryInvariance.standardReplacement p

end DaggerActualModelMainChallenge
