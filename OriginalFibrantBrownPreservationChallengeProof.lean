import ChallengeFibrantBrownPreservation

/-!
# Native Brown proof of the independent fibrant-preservation Challenge

The Challenge imports only Mathlib and states the full generic implication.
This proof uses the existing native factorization and its actual retraction.
The original EC₂ mapping theorem proves the needed trivial-fibration premise
separately; it does not assume its intended weak-equivalence conclusion.
-/

set_option autoImplicit false

open CategoryTheory HomotopicalAlgebra

universe u v u' v'

namespace DaggerOriginalFibrantBrownPreservationChallengeProof

noncomputable section

/-- The exact independently stated Challenge, with no change to its types or hypotheses. -/
theorem challengeProof : ChallengeFibrantBrownPreservation.Statement.{u, v, u', v'} := by
  intro C _ _ D _ _ F H X Y hX hY p hp
  have : IsFibrant X := hX
  have : IsFibrant Y := hY
  have : WeakEquivalence p := hp
  let h : FibrantBrownFactorization p := Classical.choice inferInstance
  have : WeakEquivalence (F.map h.p) := H h.p inferInstance inferInstance
  have : WeakEquivalence (F.map h.r) := H h.r inferInstance inferInstance
  have hi : F.map h.i ≫ F.map h.r = 𝟙 (F.obj X) := by
    rw [← F.map_comp, h.i_r, F.map_id]
  have : WeakEquivalence (F.map h.i) := weakEquivalence_of_postcomp_of_fac hi
  have hm : WeakEquivalence (F.map h.i ≫ F.map h.p) := inferInstance
  rwa [← F.map_comp, h.fac] at hm

end

end DaggerOriginalFibrantBrownPreservationChallengeProof
