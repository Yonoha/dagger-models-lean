import ChallengeActualDaggerLeftProper
import OriginalJoyalTrivialCofClosureRecovered

set_option autoImplicit false
open CategoryTheory DaggerModels
universe u

namespace DaggerActualLeftProperChallenge

theorem weak_eq_original :
    weak.{u} = DaggerJoyalWeakProperties.standardJoyalWeakEquivalences.{u} := rfl

theorem trivialCof_eq_original :
    trivialCof.{u} = DaggerJoyalTrivialCofClosure.Q
      DaggerUnitaryInvariance.standardReplacement.{u} := rfl

theorem rigidificationVerified : rigidificationStatement.{u} := by
  intro X Y i hi
  exact DaggerRigidificationCofBridge.rigidification_preserves_cofibrations i hi

theorem leftProperVerified : leftProperStatement.{u} := by
  intro X Y X' Y' f i j f' sq hi hf
  exact DaggerJoyalLeftProper.standard_leftProper sq hi hf

theorem closureVerified : closureStatement.{u} :=
  ⟨DaggerJoyalTrivialCofClosure.cobaseStable DaggerUnitaryInvariance.standardReplacement,
    DaggerJoyalTrivialCofClosure.transfiniteStable DaggerUnitaryInvariance.standardReplacement,
    DaggerJoyalTrivialCofClosure.retractStable DaggerUnitaryInvariance.standardReplacement⟩

end DaggerActualLeftProperChallenge
