import OriginalComposableTriangleIsomorphisms

/-!
# Every positive-dimensional non-edge horn filler stays in the original core

In dimension two, an outer horn supplies a diagonal and a side, so native
isomorphism cancellation gives the missing side. Inner horns use the verified
inner-horn theorem. In dimensions at least three every edge lies in the horn.
This proves membership of actual fillers; existence of outer fillers is separate.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerOriginalOrdinaryKanCoreSubcomplex
open DaggerOriginalOrdinaryKanCoreNerveMembership
open DaggerOriginalOrdinaryKanCoreEdgeMembership
open DaggerOriginalInnerHornAdjacentEdges
open DaggerOriginalOrdinaryKanCoreInnerHorns
open DaggerOriginalOrdinaryCoreHornEdgeTransport
open DaggerOriginalComposableTriangleIsomorphisms

universe u

namespace DaggerOriginalOrdinaryCoreHornFillerMembership

noncomputable section

/-- Any actual two-dimensional horn filler with core-valued horn remains in the original core. -/
theorem core_twoHorn_filler_mem (X : SSet.{u}) {i : Fin 3}
    (σ₀ : (Λ[2, i] : SSet.{u}) ⟶ (ordinaryCoreCandidate X : SSet.{u}))
    (σ : (Δ[2] : SSet.{u}) ⟶ X)
    (hσ : σ₀ ≫ (ordinaryCoreCandidate X).ι = Λ[2, i].ι ≫ σ) :
    SSet.yonedaEquiv σ ∈ (ordinaryCoreCandidate X).obj (op ⦋2⦌) := by
  fin_cases i
  · apply (mem_ordinaryCoreCandidate_iff_unit_arrows_iso X (op ⦋2⦌) _).mpr
    apply all_arrows_iso_of_triangle_diagonal
    · apply unit_map_isIso_of_core_horn_edge X σ₀ σ hσ
      exact pairOperator_mem_horn 0 0 2 (by decide) 1 (by decide) (by decide) (by decide)
    · left
      apply unit_map_isIso_of_core_horn_edge X σ₀ σ hσ
      exact pairOperator_mem_horn 0 0 1 (by decide) 2 (by decide) (by decide) (by decide)
  · exact core_innerHorn_filler_mem X (by decide) (by decide) σ₀ σ hσ
  · apply (mem_ordinaryCoreCandidate_iff_unit_arrows_iso X (op ⦋2⦌) _).mpr
    apply all_arrows_iso_of_triangle_diagonal
    · apply unit_map_isIso_of_core_horn_edge X σ₀ σ hσ
      exact pairOperator_mem_horn 2 0 2 (by decide) 1 (by decide) (by decide) (by decide)
    · right
      apply unit_map_isIso_of_core_horn_edge X σ₀ σ hσ
      exact pairOperator_mem_horn 2 1 2 (by decide) 0 (by decide) (by decide) (by decide)

/-- Every actual horn filler of dimension at least two lies in the same original core. -/
theorem core_horn_filler_mem_of_two_le (X : SSet.{u}) {n : ℕ} {i : Fin (n + 1)}
    (hn : 2 ≤ n)
    (σ₀ : (Λ[n, i] : SSet.{u}) ⟶ (ordinaryCoreCandidate X : SSet.{u}))
    (σ : (Δ[n] : SSet.{u}) ⟶ X)
    (hσ : σ₀ ≫ (ordinaryCoreCandidate X).ι = Λ[n, i].ι ≫ σ) :
    SSet.yonedaEquiv σ ∈ (ordinaryCoreCandidate X).obj (op ⦋n⦌) := by
  by_cases hn2 : n = 2
  · subst n
    exact core_twoHorn_filler_mem X σ₀ σ hσ
  · exact core_horn_filler_mem_of_three_le X (by omega) σ₀ σ hσ

/-- Any actual filler in the input for a core-valued horn of dimension at least two lifts. -/
theorem core_horn_filler_lift_of_two_le (X : SSet.{u}) {n : ℕ} {i : Fin (n + 1)}
    (hn : 2 ≤ n)
    (σ₀ : (Λ[n, i] : SSet.{u}) ⟶ (ordinaryCoreCandidate X : SSet.{u}))
    (σ : (Δ[n] : SSet.{u}) ⟶ X)
    (hσ : σ₀ ≫ (ordinaryCoreCandidate X).ι = Λ[n, i].ι ≫ σ) :
    ∃ τ : (Δ[n] : SSet.{u}) ⟶ (ordinaryCoreCandidate X : SSet.{u}),
      τ ≫ (ordinaryCoreCandidate X).ι = σ ∧ σ₀ = Λ[n, i].ι ≫ τ := by
  have hs := core_horn_filler_mem_of_two_le X hn σ₀ σ hσ
  let cs : (ordinaryCoreCandidate X : SSet.{u}).obj (op ⦋n⦌) := ⟨SSet.yonedaEquiv σ, hs⟩
  let τ : (Δ[n] : SSet.{u}) ⟶ (ordinaryCoreCandidate X : SSet.{u}) :=
    SSet.yonedaEquiv.symm cs
  have hτ : τ ≫ (ordinaryCoreCandidate X).ι = σ := by
    apply (SSet.yonedaEquiv (X := X) (n := ⦋n⦌)).injective
    rw [SSet.yonedaEquiv_comp]
    change (ordinaryCoreCandidate X).ι.app (op ⦋n⦌)
      (SSet.yonedaEquiv (SSet.yonedaEquiv.symm cs)) = SSet.yonedaEquiv σ
    rw [Equiv.apply_symm_apply]
    rfl
  refine ⟨τ, hτ, ?_⟩
  apply (cancel_mono (ordinaryCoreCandidate X).ι).mp
  rw [Category.assoc, hτ]
  exact hσ

end

end DaggerOriginalOrdinaryCoreHornFillerMembership
