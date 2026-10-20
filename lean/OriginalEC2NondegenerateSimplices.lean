import OriginalEC2SimplicialAction
import Mathlib.AlgebraicTopology.SimplicialSet.Degenerate

/-!
# Nondegenerate simplices of the actual codiscrete-nerve `E_• C₂`

No partial-order nerve theorem applies to this codiscrete category. A repeated
adjacent vertex instead gives a degeneracy preimage directly: the face that
omits that vertex. Equality of the resulting composable arrows is determined
by their vertices because every codiscrete Hom is `Unit`.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerOriginalDaggerRealizationC2Action
open DaggerOriginalEC2SimplicialAction

universe u

namespace DaggerOriginalEC2NondegenerateSimplices

noncomputable section

/-- A simplex lies in the range of one degeneracy exactly when that pair of
adjacent vertices agrees. The category is the actual `Codiscrete C2`. -/
theorem sigma_range_iff_adjacent (n : ℕ)
    (s : ComposableArrows (Codiscrete C2.{u}) (n + 1))
    (i : Fin (n + 1)) :
    s ∈ Set.range ((simplicialEC2.{u}).σ i) ↔
      s.obj i.castSucc = s.obj i.succ := by
  constructor
  · rintro ⟨t, rfl⟩
    change ((nerve (Codiscrete C2.{u})).σ i t).obj i.castSucc =
      ((nerve (Codiscrete C2.{u})).σ i t).obj i.succ
    simp [nerve.σ_obj]
  · intro h
    refine ⟨(simplicialEC2.{u}).δ i.castSucc s, ?_⟩
    apply ComposableArrows.ext
    · intro j hj
      exact @Subsingleton.elim Unit inferInstance _ _
    · intro j
      change ((nerve (Codiscrete C2.{u})).σ i
        ((nerve (Codiscrete C2.{u})).δ i.castSucc s)).obj j = s.obj j
      rw [nerve.σ_obj, nerve.δ_obj]
      by_cases h₁ : i.castSucc < j
      · obtain ⟨j, rfl⟩ := Fin.eq_succ_of_ne_zero (Fin.ne_zero_of_lt h₁)
        rw [Fin.predAbove_of_castSucc_lt _ _ h₁, Fin.pred_succ,
          Fin.succAbove_of_le_castSucc _ _ (Fin.le_castSucc_iff.2 h₁)]
      · simp only [not_lt] at h₁
        grind [SimplexCategory.len_mk, → Fin.succAbove_of_castSucc_lt,
          → Fin.predAbove_of_le_castSucc, Fin.castSucc_castPred, Fin.castPred_castSucc,
          Fin.succAbove_castSucc_self, → LE.le.lt_or_eq]

/-- Actual nondegeneracy is equivalent to having no repeated adjacent object. -/
theorem nondegenerate_iff_adjacent_ne (n : ℕ)
    (s : ComposableArrows (Codiscrete C2.{u}) n) :
    s ∈ (simplicialEC2.{u}).nonDegenerate n ↔
      ∀ i : Fin n, s.obj i.castSucc ≠ s.obj i.succ := by
  cases n with
  | zero =>
      constructor
      · intro _ i
        exact Fin.elim0 i
      · intro _
        simp
  | succ n =>
      rw [SSet.mem_nonDegenerate_iff_notMem_degenerate,
        (simplicialEC2.{u}).degenerate_eq_iUnion_range_σ]
      constructor
      · intro hs i heq
        apply hs
        exact Set.mem_iUnion.mpr ⟨i, (sigma_range_iff_adjacent n s i).2 heq⟩
      · intro hs hdeg
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hdeg
        exact hs i ((sigma_range_iff_adjacent n s i).1 hi)

/-- The same criterion written in the paper's underlying `C2` labels. -/
theorem nondegenerate_iff_adjacent_labels (n : ℕ)
    (s : ComposableArrows (Codiscrete C2.{u}) n) :
    s ∈ (simplicialEC2.{u}).nonDegenerate n ↔
      ∀ i : Fin n, (s.obj i.castSucc).as ≠ (s.obj i.succ).as := by
  rw [nondegenerate_iff_adjacent_ne]
  constructor
  · intro h i heq
    exact h i (Codiscrete.ext heq)
  · intro h i heq
    exact h i (congrArg Codiscrete.as heq)

end

end DaggerOriginalEC2NondegenerateSimplices
