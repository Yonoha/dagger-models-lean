import ProofActualMainTheoremB
import ProofOriginalMainTheoremC
import ProofActualMainTheoremD

/-! Public entry points for the three independently frozen Lean main statements.
The statements use the original project definitions; they are not Mathlib-only specifications.
-/
set_option autoImplicit false
universe u

namespace DaggerComparator

/-- The original dagger Joyal model and its original Quillen equivalence. -/
theorem mainB : DaggerActualMainTheoremBChallenge.statement.{u} :=
  DaggerActualMainTheoremBProof.verified

/-- Intrinsic recognition for every original dagger quasi-category map. -/
theorem originalMainTheoremC : DaggerChallengeOriginalMainTheoremC.Statement.{u} :=
  DaggerProofOriginalMainTheoremC.verified

/-- The original anti-involutive model and both original non-Quillen conclusions. -/
theorem mainD : ChallengeActualMainTheoremD.Statement.{u} :=
  ProofActualMainTheoremD.verified

end DaggerComparator
