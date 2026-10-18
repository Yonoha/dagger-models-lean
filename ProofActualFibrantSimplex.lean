import ChallengeActualFibrantSimplex
import ActualFibrantSimplexContractibility

/-! The new challenge compiles together with the actual previous model-category context. -/
set_option autoImplicit false
universe u
namespace DaggerActualFibrantSimplexProof

theorem verified : DaggerActualFibrantSimplexChallenge.statement.{u} := by
  refine ⟨?_, ?_, ?_⟩
  · intro A _ _
    exact ⟨DaggerActualThinConstantCoherentNerve.coherentNerveIso A⟩
  · intro X Y p hX hY
    exact DaggerNativeKanFibrationToSubsingleton.fibration p hX hY
  · exact DaggerActualFibrantSimplexContractibility.simplex_gadget_hom_toUnit_GW

end DaggerActualFibrantSimplexProof
