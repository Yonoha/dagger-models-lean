import OriginalComposableArrowsAdjacentIsomorphisms

/-!
# Every adjacent edge belongs to the actual inner horn

Use the original ordered-pair simplex operator. A vertex outside its two endpoints
and different from the omitted face proves membership in the literal horn.
For inner horns either the first or the last vertex provides such a vertex.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerOriginalOrdinaryKanCoreEdgeMembership

universe u

namespace DaggerOriginalInnerHornAdjacentEdges

/-- An original ordered-pair edge belongs to a horn when a third vertex is still omitted. -/
theorem pairOperator_mem_horn {n : ℕ} (i a b : Fin (n + 1)) (hab : a ≤ b)
    (j : Fin (n + 1)) (hja : j ≠ a) (hjb : j ≠ b) (hji : j ≠ i) :
    (SSet.stdSimplex.objEquiv.symm (pairOperator a b hab) : (Δ[n] : SSet.{u}).obj (op ⦋1⦌)) ∈
      (Λ[n, i]).obj (op ⦋1⦌) := by
  change Set.range (pairOperator a b hab).toOrderHom ∪ {i} ≠ Set.univ
  intro heq
  have hj : j ∈ Set.range (pairOperator a b hab).toOrderHom ∪ {i} := by
    rw [heq]
    trivial
  rcases hj with ⟨t, ht⟩ | hj
  · change (if t = 0 then a else b) = j at ht
    split_ifs at ht
    · exact hja ht.symm
    · exact hjb ht.symm
  · exact hji (Set.mem_singleton_iff.mp hj)

/-- All genuine adjacent edges lie in every actual inner horn, in arbitrary universe. -/
theorem adjacentOperator_mem_innerHorn {n : ℕ} (i : Fin (n + 1))
    (h0 : 0 < i) (hn : i < Fin.last n) (k : Fin n) :
    (SSet.stdSimplex.objEquiv.symm
      (pairOperator k.castSucc k.succ (Fin.castSucc_le_succ k)) :
        (Δ[n] : SSet.{u}).obj (op ⦋1⦌)) ∈ (Λ[n, i]).obj (op ⦋1⦌) := by
  by_cases hk : k.val = 0
  · apply pairOperator_mem_horn i k.castSucc k.succ (Fin.castSucc_le_succ k) (Fin.last n)
    · intro hj
      have hv := congrArg Fin.val hj
      simp only [Fin.val_last, Fin.val_castSucc] at hv
      have hkn := k.isLt
      omega
    · intro hj
      have hv := congrArg Fin.val hj
      simp only [Fin.val_last, Fin.val_succ] at hv
      change 0 < i.val at h0
      change i.val < n at hn
      omega
    · exact ne_of_gt hn
  · apply pairOperator_mem_horn i k.castSucc k.succ (Fin.castSucc_le_succ k) 0
    · intro hj
      have hv := congrArg Fin.val hj
      simp only [Fin.val_zero, Fin.val_castSucc] at hv
      exact hk hv.symm
    · intro hj
      have hv := congrArg Fin.val hj
      simp only [Fin.val_zero, Fin.val_succ] at hv
      omega
    · exact ne_of_lt h0

end DaggerOriginalInnerHornAdjacentEdges
