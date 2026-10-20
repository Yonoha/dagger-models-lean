import ChallengeActualDaggerModel
import OriginalActualDaggerModelConstruction

set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra DaggerModels
universe u

namespace DaggerActualModelChallenge

theorem weak_eq_original :
    weak.{u} = DaggerJoyalWeakProperties.standardJoyalWeakEquivalences.{u} := rfl

theorem verified : statement.{u} := by
  refine ⟨DaggerOriginalJoyalModel.standardModelCategory, ?_, ?_, ?_⟩
  · cases h : DaggerOriginalJoyalModel.standardModelCategory.{u}.categoryWithWeakEquivalences
    apply congrArg CategoryWithWeakEquivalences.mk
    simpa only [h] using DaggerOriginalJoyalModel.standard_model_weak.{u}
  · cases h : DaggerOriginalJoyalModel.standardModelCategory.{u}.categoryWithCofibrations
    apply congrArg CategoryWithCofibrations.mk
    simpa only [h] using DaggerOriginalJoyalModel.standard_model_cof.{u}
  · cases h : DaggerOriginalJoyalModel.standardModelCategory.{u}.categoryWithFibrations
    apply congrArg CategoryWithFibrations.mk
    simpa only [h] using DaggerOriginalJoyalModel.standard_model_fib.{u}

theorem generationVerified : generationStatement.{u} := by
  refine ⟨DaggerActualWeakAccessibility.NamespaceGate.actualDaggerSetLP,
    DaggerActualWeakAccessibility.originalID_small,
    DaggerOriginalJoyalModel.originalID_rlp_llp_eq_freeCofibrations,
    DaggerOriginalJoyalModel.generatedJ DaggerUnitaryInvariance.standardReplacement, ?_, ?_⟩
  · exact DaggerOriginalJoyalModel.generatedJ_small DaggerUnitaryInvariance.standardReplacement
  · exact DaggerOriginalJoyalModel.generatedJ_trivialCofibrations
      DaggerUnitaryInvariance.standardReplacement

end DaggerActualModelChallenge
