import ProofTheoremA

/-! A-only public alias. The existing B/C/D aliases and targets are unchanged. -/

set_option autoImplicit false
universe u

namespace DaggerComparator

/-- The exact dagger Bergner model, its finite generating data and left properness. -/
theorem mainA : DaggerTheoremAChallenge.statement.{u} :=
  DaggerTheoremAProof.verified

end DaggerComparator
