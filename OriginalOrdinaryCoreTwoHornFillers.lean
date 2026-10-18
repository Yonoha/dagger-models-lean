import OriginalQuasicategoryOuterTwoHorns

/-!
# Every actual two-horn fills in the same original core

The original core inclusion sends each edge to an edge invertible under the
same original unit. The proved outer-two-horn constructions therefore fill in
the original input. The actual filler-membership theorem lifts those fillers
into the same original core. Inner two-horns use its proved inner-horn property.
No candidate Kan property is assumed; higher outer horns remain separate.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerOriginalOrdinaryKanCoreSubcomplex
open DaggerOriginalOrdinaryKanCoreEdgeMembership
open DaggerOriginalOrdinaryKanCoreEdgeMaximality
open DaggerOriginalInnerHornFillers
open DaggerOriginalOrdinaryKanCoreInnerHorns
open DaggerOriginalOrdinaryCoreHornFillerMembership
open DaggerOriginalQuasicategoryOuterTwoHorns

universe u

namespace DaggerOriginalOrdinaryCoreTwoHornFillers

noncomputable section

/-- Every actual left outer two-horn fills in the original core without a Kan premise. -/
theorem core_outer20_filling (X : SSet.{u}) (hX : innerHornFillers X)
    (σ₀ : (Λ[2, 0] : SSet.{u}) ⟶ (ordinaryCoreCandidate X : SSet.{u})) :
    ∃ σ : (Δ[2] : SSet.{u}) ⟶ (ordinaryCoreCandidate X : SSet.{u}),
      σ₀ = Λ[2, 0].ι ≫ σ := by
  have hedge : ∀ e : (ordinaryCoreCandidate X : SSet.{u}).obj (op ⦋1⦌),
      edgeIsInvertible X ((ordinaryCoreCandidate X).ι.app (op ⦋1⦌) e) := by
    intro e
    exact (mem_ordinaryCoreCandidate_one_iff X e.val).mp e.property
  obtain ⟨σ, hσ⟩ := outer20_filling hX (ordinaryCoreCandidate X).ι hedge σ₀
  obtain ⟨τ, _, hτ⟩ := core_horn_filler_lift_of_two_le X (by decide) σ₀ σ hσ
  exact ⟨τ, hτ⟩

/-- Every actual right outer two-horn fills in the original core without a Kan premise. -/
theorem core_outer22_filling (X : SSet.{u}) (hX : innerHornFillers X)
    (σ₀ : (Λ[2, 2] : SSet.{u}) ⟶ (ordinaryCoreCandidate X : SSet.{u})) :
    ∃ σ : (Δ[2] : SSet.{u}) ⟶ (ordinaryCoreCandidate X : SSet.{u}),
      σ₀ = Λ[2, 2].ι ≫ σ := by
  have hedge : ∀ e : (ordinaryCoreCandidate X : SSet.{u}).obj (op ⦋1⦌),
      edgeIsInvertible X ((ordinaryCoreCandidate X).ι.app (op ⦋1⦌) e) := by
    intro e
    exact (mem_ordinaryCoreCandidate_one_iff X e.val).mp e.property
  obtain ⟨σ, hσ⟩ := outer22_filling hX (ordinaryCoreCandidate X).ι hedge σ₀
  obtain ⟨τ, _, hτ⟩ := core_horn_filler_lift_of_two_le X (by decide) σ₀ σ hσ
  exact ⟨τ, hτ⟩

/-- All three actual two-horns fill in the same original core, in arbitrary universe. -/
theorem core_twoHorn_filling (X : SSet.{u}) (hX : innerHornFillers X)
    {i : Fin 3}
    (σ₀ : (Λ[2, i] : SSet.{u}) ⟶ (ordinaryCoreCandidate X : SSet.{u})) :
    ∃ σ : (Δ[2] : SSet.{u}) ⟶ (ordinaryCoreCandidate X : SSet.{u}),
      σ₀ = Λ[2, i].ι ≫ σ := by
  fin_cases i
  · exact core_outer20_filling X hX σ₀
  · exact innerHornFillers_ordinaryCoreCandidate X hX (by decide) (by decide) σ₀
  · exact core_outer22_filling X hX σ₀

end

end DaggerOriginalOrdinaryCoreTwoHornFillers
