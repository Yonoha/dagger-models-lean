import OriginalOrdinaryKanCoreInnerHorns

/-!
# Edges in the original higher-dimensional horns

A horn in dimension at least three contains every ordered-pair edge. Choose a
vertex outside the two endpoints and the omitted face using Mathlib's finite
cardinality lemma, then apply the literal horn membership criterion.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerOriginalOrdinaryKanCoreEdgeMembership
open DaggerOriginalInnerHornAdjacentEdges

universe u

namespace DaggerOriginalHornEdgesMembership

/-- Every actual ordered-pair edge lies in any horn of dimension at least three. -/
theorem pairOperator_mem_horn_of_three_le {n : ℕ} (hn : 3 ≤ n)
    (i a b : Fin (n + 1)) (hab : a ≤ b) :
    (SSet.stdSimplex.objEquiv.symm (pairOperator a b hab) :
      (Δ[n] : SSet.{u}).obj (op ⦋1⦌)) ∈ (Λ[n, i]).obj (op ⦋1⦌) := by
  have hcard : ({a, b, i} : Finset (Fin (n + 1))).card <
      (Finset.univ : Finset (Fin (n + 1))).card := by
    calc
      ({a, b, i} : Finset (Fin (n + 1))).card ≤ 3 := Finset.card_le_three
      _ < (Finset.univ : Finset (Fin (n + 1))).card := by
        simp only [Finset.card_univ, Fintype.card_fin]
        omega
  obtain ⟨j, _, hj⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
  exact pairOperator_mem_horn i a b hab j hj.1 hj.2.1 hj.2.2

end DaggerOriginalHornEdgesMembership
