import OriginalJoinedHornPrefix

/-!
# Native joined cofaces and preservation of original prefix vertices

The native ordinal-sum map acts separately on the two original blocks. Its
right coface is exactly the original coface with shifted index k+1+i. No map
from the right block can enter the left block. These identities supply the
coface and boundary compatibility needed to glue actual coslice horn data.
-/

set_option autoImplicit false

open CategoryTheory Simplicial
open DaggerOriginalOrdinalJoinLeft
open DaggerOriginalJoinedHornGeometry

namespace DaggerOriginalJoinedCofaces

/-- Every original joined vertex lies in exactly one of the two native ordinal blocks. -/
theorem vertex_eq_prefix_or_suffix (k n : ℕ) (j : Fin (k + n + 2)) :
    (∃ a : Fin (k + 1), j = prefixIndex k n a) ∨
      ∃ a : Fin (n + 1), j = suffixIndex k n a := by
  by_cases h : j.val < k + 1
  · exact Or.inl ⟨⟨j.val, h⟩, Fin.ext rfl⟩
  · refine Or.inr ⟨⟨j.val - (k + 1), by have hj := j.isLt; omega⟩, ?_⟩
    apply Fin.ext
    change j.val = k + 1 + (j.val - (k + 1))
    omega

/-- The native ordinal-join map fixes each original left-block vertex. -/
theorem joinMap_prefix_eval (k : ℕ) {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌)
    (j : Fin (k + 1)) :
    ((ordinalJoinLeft ⦋k⦌).map α).toOrderHom (prefixIndex k m j) = prefixIndex k n j := by
  rw [prefixIndex_eq_native, prefixIndex_eq_native]
  exact congrArg (fun g : ⦋k⦌ ⟶ ⦋k + n + 1⦌ ↦ g.toOrderHom j) (prefix_comp (k := ⦋k⦌) α)

/-- The native ordinal-join map applies the original operator to each right-block vertex. -/
theorem joinMap_suffix_eval (k : ℕ) {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌)
    (j : Fin (m + 1)) :
    ((ordinalJoinLeft ⦋k⦌).map α).toOrderHom (suffixIndex k m j) =
      suffixIndex k n (α.toOrderHom j) := by
  rw [suffixIndex_eq_native, suffixIndex_eq_native]
  exact congrArg (fun g : ⦋m⦌ ⟶ ⦋k + n + 1⦌ ↦ g.toOrderHom j) (suffix_comp (k := ⦋k⦌) α)

/-- The literal coface of the right joined block is the native coface with shifted index. -/
theorem joinMap_coface (k n : ℕ) (i : Fin (n + 2)) :
    (ordinalJoinLeft ⦋k⦌).map (SimplexCategory.δ i) =
      SimplexCategory.δ (suffixIndex k (n + 1) i) := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext j
  rcases vertex_eq_prefix_or_suffix k n j with ⟨a, rfl⟩ | ⟨a, rfl⟩
  · rw [joinMap_prefix_eval]
    change prefixIndex k (n + 1) a =
      (suffixIndex k (n + 1) i).succAbove (prefixIndex k n a)
    rw [Fin.succAbove_of_castSucc_lt _ _ (by
      change a.val < k + 1 + i.val
      have ha := a.isLt
      omega)]
    exact Fin.ext rfl
  · rw [joinMap_suffix_eval]
    change suffixIndex k (n + 1) (i.succAbove a) =
      (suffixIndex k (n + 1) i).succAbove (suffixIndex k n a)
    by_cases h : a.castSucc < i
    · rw [Fin.succAbove_of_castSucc_lt i a h,
        Fin.succAbove_of_castSucc_lt _ _ (by
          change k + 1 + a.val < k + 1 + i.val
          change a.val < i.val at h
          omega)]
      exact Fin.ext rfl
    · have hh : i ≤ a.castSucc := le_of_not_gt h
      rw [Fin.succAbove_of_le_castSucc i a hh,
        Fin.succAbove_of_le_castSucc _ _ (by
          change k + 1 + i.val ≤ k + 1 + a.val
          change i.val ≤ a.val at hh
          omega)]
      exact Fin.ext rfl

/-- An original left vertex has exactly its original left vertex as preimage under the join. -/
theorem joinMap_eq_prefix_iff (k : ℕ) {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌)
    (j : Fin (k + m + 2)) (a : Fin (k + 1)) :
    ((ordinalJoinLeft ⦋k⦌).map α).toOrderHom j = prefixIndex k n a ↔
      j = prefixIndex k m a := by
  constructor
  · intro h
    rcases vertex_eq_prefix_or_suffix k m j with ⟨b, rfl⟩ | ⟨b, rfl⟩
    · rw [joinMap_prefix_eval] at h
      have hv := congrArg Fin.val h
      change b.val = a.val at hv
      have hba : b = a := Fin.ext hv
      rw [hba]
    · rw [joinMap_suffix_eval] at h
      exact False.elim (prefixIndex_ne_suffixIndex k n a (α.toOrderHom b) h.symm)
  · intro h
    rw [h, joinMap_prefix_eval]

end DaggerOriginalJoinedCofaces
