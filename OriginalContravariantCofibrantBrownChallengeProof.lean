import ChallengeContravariantCofibrantBrown

/-!
# Contravariant Brown preservation from the actual native factorization

Use the existing cofibrant Brown factorization and its literal section. No
opposite model structure or changed weak-equivalence class is needed.
-/
set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra
universe u v u' v'
namespace DaggerOriginalContravariantCofibrantBrownChallengeProof
noncomputable section

/-- The independent contravariant statement reuses Mathlib's cofibrant Brown factorization. -/
theorem challengeProof : ChallengeContravariantCofibrantBrown.Statement.{u, v, u', v'} := by
  intro C _ _ D _ _ F H X Y hX hY f hf
  have : IsCofibrant X := hX
  have : IsCofibrant Y := hY
  have : WeakEquivalence f := hf
  let h : CofibrantBrownFactorization f := Classical.choice inferInstance
  have : WeakEquivalence (F.map h.i.op) := H h.i inferInstance inferInstance
  have : WeakEquivalence (F.map h.s.op) := H h.s inferInstance inferInstance
  have hs : F.map h.p.op ≫ F.map h.s.op = 𝟙 (F.obj (Opposite.op Y)) := by
    rw [← F.map_comp, ← op_comp, h.s_p, op_id, F.map_id]
  have : WeakEquivalence (F.map h.p.op) := weakEquivalence_of_postcomp_of_fac hs
  have hm : WeakEquivalence (F.map h.p.op ≫ F.map h.i.op) := inferInstance
  rwa [← F.map_comp, ← op_comp, h.fac] at hm

end
end DaggerOriginalContravariantCofibrantBrownChallengeProof
