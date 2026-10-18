import Mathlib.AlgebraicTopology.SimplicialSet.NerveNondegenerate

/-!
# Adjacent equal vertices detect degeneracy in the nerve of any thin category

Reuse the original nerve face and degeneracy operators. No partial order or
antisymmetry is assumed, so the criterion applies to walking-isomorphism categories.
-/
set_option autoImplicit false
open CategoryTheory Simplicial
universe u v
namespace DaggerThinNerveAdjacentDegeneracy
variable {C : Type u} [Category.{v} C] [Quiver.IsThin C]

theorem mem_range_sigma_iff {n : ℕ} (s : (nerve C) _⦋n + 1⦌) (i : Fin (n + 1)) :
    s ∈ Set.range ((nerve C).σ i) ↔ s.obj i.castSucc = s.obj i.succ := by
  constructor
  · rintro ⟨s, rfl⟩
    simp [nerve.σ_obj]
  · intro h
    refine ⟨(nerve C).δ i.castSucc s, ?_⟩
    apply nerve.ext_of_isThin
    funext j
    rw [nerve.σ_obj, nerve.δ_obj]
    by_cases h₁ : i.castSucc < j
    · obtain ⟨j, rfl⟩ := Fin.eq_succ_of_ne_zero (Fin.ne_zero_of_lt h₁)
      rw [Fin.predAbove_of_castSucc_lt _ _ h₁, Fin.pred_succ,
        Fin.succAbove_of_le_castSucc _ _ (Fin.le_castSucc_iff.2 h₁)]
    · simp only [not_lt] at h₁
      grind [SimplexCategory.len_mk, → Fin.succAbove_of_castSucc_lt,
        → Fin.predAbove_of_le_castSucc, Fin.castSucc_castPred, Fin.castPred_castSucc,
        Fin.succAbove_castSucc_self, → LE.le.lt_or_eq]

theorem nonDegenerate_iff {n : ℕ} (s : (nerve C) _⦋n + 1⦌) :
    s ∈ (nerve C).nonDegenerate (n + 1) ↔
      ∀ i : Fin (n + 1), s.obj i.castSucc ≠ s.obj i.succ := by
  rw [← not_iff_not, ← SSet.mem_degenerate_iff_notMem_nonDegenerate,
    SSet.degenerate_eq_iUnion_range_σ, Set.mem_iUnion]
  simp only [mem_range_sigma_iff, not_forall, not_not]

end DaggerThinNerveAdjacentDegeneracy
