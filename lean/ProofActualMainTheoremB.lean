import ChallengeActualMainTheoremB
import ProofActualDaggerModelMain
import ProofActualDaggerQuillenEquivalence

/-! Assemble the previous exact model theorem and the newly proved actual Quillen equivalence. -/
set_option autoImplicit false
open HomotopicalAlgebra
universe u
namespace DaggerActualMainTheoremBProof
noncomputable section

local instance : ModelCategory DaggerActualRigidificationQuillen.D.{u} :=
  DaggerActualRigidificationQuillen.modelD.{u}
local instance : ModelCategory DaggerActualRigidificationQuillen.G.{u} :=
  DaggerActualRigidificationQuillen.modelG.{u}

/-- Reuse the already constructed same standard model with every original clause. -/
theorem model_verified : DaggerActualMainTheoremBChallenge.modelStatement.{u} := by
  refine ⟨?_, DaggerActualModelChallenge.generationVerified,
    DaggerActualLeftProperChallenge.leftProperVerified, ?_⟩
  · exact ⟨DaggerOriginalJoyalModel.standard_model_weak,
      DaggerOriginalJoyalModel.standard_model_cof, DaggerOriginalJoyalModel.standard_model_fib⟩
  · intro X Y p
    exact DaggerOriginalJoyalModel.trivialFibration_iff_ordinary_trivial
      DaggerUnitaryInvariance.standardReplacement p

/-- Prove all of the independently fixed Theorem B without a supplied model or comparison premise. -/
theorem verified : DaggerActualMainTheoremBChallenge.statement.{u} :=
  ⟨model_verified, DaggerActualDaggerQuillenEquivalenceProof.quillen_verified⟩

end
end DaggerActualMainTheoremBProof
