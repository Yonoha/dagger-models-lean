import ChallengeActualMainTheoremD
import ActualDCHRightInducedAndMainTheoremD

set_option autoImplicit false
universe u
namespace ProofActualMainTheoremD

theorem verified : ChallengeActualMainTheoremD.Statement.{u} := by
  refine ⟨DaggerActualDCHRightInducedAndMainTheoremD.model, ?_⟩
  exact ⟨DaggerActualDCHRightInducedAndMainTheoremD.cofibration_iff_normal,
    DaggerActualDCHRightInducedAndMainTheoremD.weakEquivalence_iff_original,
    DaggerActualDCHRightInducedAndMainTheoremD.fibration_iff_underlying_candidate,
    DaggerActualDCHRightInducedAndMainTheoremD.both_not_quillen,
    DaggerActualDCHRightInducedAndMainTheoremD.cofibrations_not_restriction⟩

end ProofActualMainTheoremD
