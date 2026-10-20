import ChallengeCofibrantBrownPreservation

/-!
# Brown preservation using the native cofibrant factorization

Prove exactly the independent Mathlib-only statement. The factorization has a
cofibration section of its trivial fibration, so preservation of trivial cofibrations
and two-out-of-three suffice. No preservation of the requested weak equivalence is assumed.
-/
set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra
universe u v u' v'
namespace DaggerOriginalCofibrantBrownPreservationChallengeProof
noncomputable section

/-- The exact independent statement, using the actual native section and factorization. -/
theorem challengeProof : ChallengeCofibrantBrownPreservation.Statement.{u, v, u', v'} := by
  intro C _ _ D _ _ F H X Y hX hY f hf
  have : IsCofibrant X := hX
  have : IsCofibrant Y := hY
  have : WeakEquivalence f := hf
  let h : CofibrantBrownFactorization f := Classical.choice inferInstance
  have : WeakEquivalence (F.map h.i) := H h.i inferInstance inferInstance
  have : WeakEquivalence (F.map h.s) := H h.s inferInstance inferInstance
  have hs : F.map h.s ≫ F.map h.p = 𝟙 (F.obj Y) := by
    rw [← F.map_comp, h.s_p, F.map_id]
  have : WeakEquivalence (F.map h.p) := weakEquivalence_of_precomp_of_fac hs
  have hm : WeakEquivalence (F.map h.i ≫ F.map h.p) := inferInstance
  rwa [← F.map_comp, h.fac] at hm

end
end DaggerOriginalCofibrantBrownPreservationChallengeProof
