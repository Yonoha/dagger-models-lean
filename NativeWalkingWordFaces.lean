import NativeWalkingSimplexWords
import TopCatModelCategory.SSet.PairingCore

/-! Nondegeneracy and unique face indices in the original walking-interval product. -/
set_option autoImplicit false
open CategoryTheory Simplicial MonoidalCategory
open DaggerActualFreeWalkingIsoIntegerObstruction DaggerNativeWalkingSimplexWords
universe u
namespace DaggerNativeWalkingWordFaces
noncomputable section

theorem coordinates_delta {n d : ℕ} (x : (Δ[n] ⊗ J.{u} : SSet.{u}) _⦋d + 1⦌)
    (i : Fin (d + 2)) (j : Fin (d + 1)) :
    (coordinates ((Δ[n] ⊗ J.{u}).δ i x)).val j =
      (coordinates x).val (i.succAbove j) := rfl

theorem coordinates_sigma {n d : ℕ} (x : (Δ[n] ⊗ J.{u} : SSet.{u}) _⦋d⦌)
    (i : Fin (d + 1)) (j : Fin (d + 2)) :
    (coordinates ((Δ[n] ⊗ J.{u}).σ i x)).val j =
      (coordinates x).val (i.predAbove j) := rfl

theorem mem_range_sigma_iff {n d : ℕ} (x : (Δ[n] ⊗ J.{u} : SSet.{u}) _⦋d + 1⦌)
    (i : Fin (d + 1)) : x ∈ Set.range ((Δ[n] ⊗ J.{u}).σ i) ↔
      (coordinates x).val i.castSucc = (coordinates x).val i.succ := by
  constructor
  · rintro ⟨x, rfl⟩
    simp only [coordinates_sigma]
    simp
  · intro h
    refine ⟨(Δ[n] ⊗ J.{u}).δ i.castSucc x, ?_⟩
    apply (wordEquiv n (d + 1)).injective
    apply Subtype.ext
    funext j
    change (coordinates ((Δ[n] ⊗ J.{u}).σ i ((Δ[n] ⊗ J.{u}).δ i.castSucc x))).val j =
      (coordinates x).val j
    rw [coordinates_sigma, coordinates_delta]
    by_cases hj : j = i.castSucc
    · subst hj
      simpa using h.symm
    · rw [Fin.succAbove_predAbove hj]

theorem nonDegenerate_iff {n d : ℕ} (x : (Δ[n] ⊗ J.{u} : SSet.{u}) _⦋d + 1⦌) :
    x ∈ (Δ[n] ⊗ J.{u}).nonDegenerate (d + 1) ↔
      ∀ i : Fin (d + 1), (coordinates x).val i.castSucc ≠ (coordinates x).val i.succ := by
  rw [← not_iff_not, ← SSet.mem_degenerate_iff_notMem_nonDegenerate,
    SSet.degenerate_eq_iUnion_range_σ, Set.mem_iUnion]
  simp only [mem_range_sigma_iff, not_forall, not_not]

theorem delta_ne_of_lt {n d : ℕ} (x : (Δ[n] ⊗ J.{u} : SSet.{u}) _⦋d + 1⦌)
    (hx : x ∈ (Δ[n] ⊗ J.{u}).nonDegenerate (d + 1)) (i j : Fin (d + 2)) (hij : i < j) :
    (Δ[n] ⊗ J.{u}).δ i x ≠ (Δ[n] ⊗ J.{u}).δ j x := by
  intro h
  obtain ⟨i, rfl⟩ := Fin.eq_castSucc_of_ne_last (Fin.ne_last_of_lt hij)
  have hc := congrArg (fun t ↦ (coordinates t).val i) h
  dsimp only at hc
  rw [coordinates_delta, coordinates_delta, Fin.succAbove_castSucc_self,
    Fin.succAbove_of_castSucc_lt _ _ hij] at hc
  exact (nonDegenerate_iff x).mp hx i hc.symm

theorem delta_injective {n d : ℕ} (x : (Δ[n] ⊗ J.{u} : SSet.{u}) _⦋d + 1⦌)
    (hx : x ∈ (Δ[n] ⊗ J.{u}).nonDegenerate (d + 1)) :
    Function.Injective (fun i ↦ (Δ[n] ⊗ J.{u}).δ i x) := by
  intro i j h
  by_contra hij
  obtain hij | hij := lt_or_gt_of_ne hij
  · exact delta_ne_of_lt x hx i j hij h
  · exact delta_ne_of_lt x hx j i hij h.symm

theorem uniquelyCodimOneFace {n d : ℕ} (x : (Δ[n] ⊗ J.{u} : SSet.{u}) _⦋d + 1⦌)
    (hx : x ∈ (Δ[n] ⊗ J.{u}).nonDegenerate (d + 1)) (i : Fin (d + 2)) :
    SSet.IsUniquelyCodimOneFace ((Δ[n] ⊗ J.{u}).δ i x) x :=
  .mk ⟨i, rfl, fun _ h ↦ delta_injective x hx h⟩

end
end DaggerNativeWalkingWordFaces
