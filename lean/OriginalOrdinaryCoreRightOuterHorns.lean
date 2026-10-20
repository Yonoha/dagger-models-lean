import OriginalRightOuterHornFilling
import OriginalOrdinaryCoreHornFillerMembership
import OriginalOrdinaryKanCoreEdgeMaximality

/-!
# All original right outer horns fill in the original ordinary core

The supplied core edge has invertible image under the original homotopy-category
unit. Fill the actual ambient right outer horn with the verified all-dimensional
theorem, then use the original whole-horn filler-membership theorem to lift the
same filler into the same core. No Kan property of the core is assumed.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerOriginalOrdinaryKanCoreSubcomplex DaggerOriginalOrdinaryKanCoreEdgeMembership
open DaggerOriginalOrdinaryKanCoreEdgeMaximality DaggerOriginalInnerHornFillers
open DaggerOriginalOrdinaryCoreHornFillerMembership DaggerOriginalRightOuterHornInclusions
open DaggerOriginalRightOuterHornFilling

universe u

namespace DaggerOriginalOrdinaryCoreRightOuterHorns

noncomputable section

/-- Every actual right outer horn in dimension at least two fills in the exact original core. -/
theorem core_right_outer_horn_filler (X : SSet.{u}) (hX : innerHornFillers X) (k : ℕ)
    (φ : (Λ[k + 2, Fin.last (k + 2)] : SSet.{u}) ⟶ (ordinaryCoreCandidate X : SSet.{u})) :
    ∃ σ : (Δ[k + 2] : SSet.{u}) ⟶ (ordinaryCoreCandidate X : SSet.{u}),
      φ = Λ[k + 2, Fin.last (k + 2)].ι ≫ σ := by
  have he : edgeIsInvertible X (SSet.yonedaEquiv
      (rightOuterLastEdgeInclusion k ≫ (φ ≫ (ordinaryCoreCandidate X).ι))) := by
    rw [← Category.assoc, SSet.yonedaEquiv_comp]
    exact (mem_ordinaryCoreCandidate_one_iff X _).mp
      (SSet.yonedaEquiv (rightOuterLastEdgeInclusion k ≫ φ)).property
  obtain ⟨σ, hσ⟩ := right_outer_horn_filler hX k (φ ≫ (ordinaryCoreCandidate X).ι) he
  obtain ⟨τ, _, hτ⟩ := core_horn_filler_lift_of_two_le X (by omega) φ σ hσ
  exact ⟨τ, hτ⟩

end

end DaggerOriginalOrdinaryCoreRightOuterHorns
