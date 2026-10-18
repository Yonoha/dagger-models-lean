import ActualQRealizationQuillen
import OriginalFibrantBrownPreservationChallengeProof

/-! The unchanged original-Q singular functor preserves weak maps between Kan objects. -/

set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra
open DaggerOriginalCounitRightConeQRealizationAdjunction DaggerSSetGluing
open DaggerOriginalCounitRightConeQRealizationCofibrations
open scoped SSet.modelCategoryQuillen
universe u

namespace DaggerActualQSingularFibrantWeakEquivalences
noncomputable section

/-- Apply the existing native Brown theorem to the literal singular functor. -/
theorem singular_weakEquivalence {X Y : SSet.{u}} (f : X ⟶ Y)
    [IsFibrant X] [IsFibrant Y] [WeakEquivalence f] :
    WeakEquivalence (singular.{u}.map f) := by
  exact DaggerOriginalFibrantBrownPreservationChallengeProof.challengeProof
    SSet SSet singular (by
      intro A B p hp hw
      have : Fibration p := hp
      have : WeakEquivalence p := hw
      exact ((mem_trivialFibrations_iff _).1 (singular_trivialFibration p)).2)
    inferInstance inferInstance f inferInstance

/-- This is the same geometric weak-equivalence predicate used for the original counit. -/
theorem singular_GW {X Y : SSet.{u}} (f : X ⟶ Y) [X.KanComplex] [Y.KanComplex]
    (hf : GW f) : GW (singular.{u}.map f) := by
  have : WeakEquivalence f := (weakEquivalence_iff_GW f).2 hf
  exact (weakEquivalence_iff_GW _).1 (singular_weakEquivalence f)

end
end DaggerActualQSingularFibrantWeakEquivalences
