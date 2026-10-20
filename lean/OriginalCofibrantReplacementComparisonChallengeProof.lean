import ChallengeCofibrantReplacementComparison

/-!
# Comparison over the exact target in a native model category

Use Mathlib's lifting square for the actual initial map, followed by native
two-out-of-three. The statement keeps the full morphisms and their exact triangle.
It does not assert invariance of an arbitrary enriched mapping object.
-/
set_option autoImplicit false
open CategoryTheory Limits HomotopicalAlgebra
universe u v
namespace DaggerOriginalCofibrantReplacementComparisonChallengeProof
noncomputable section

/-- The independent comparison statement follows from the native model lifting axiom. -/
theorem challengeProof : ChallengeCofibrantReplacementComparison.Statement.{u, v} := by
  intro C _ _ X Y T hX q p hq hp hwp
  have : IsCofibrant X := hX
  have : WeakEquivalence q := hq
  have : Fibration p := hp
  have : WeakEquivalence p := hwp
  have : Cofibration (initial.to X) := (isCofibrant_iff X).1 inferInstance
  let sq : CommSq (initial.to Y) (initial.to X) p q :=
    ⟨initialIsInitial.hom_ext _ _⟩
  refine ⟨sq.lift, sq.fac_right, ?_⟩
  have : WeakEquivalence (sq.lift ≫ p) := by rw [sq.fac_right]; infer_instance
  exact weakEquivalence_of_postcomp sq.lift p

end
end DaggerOriginalCofibrantReplacementComparisonChallengeProof
