import TopCatModelCategory.Fin

/-! Deleting an interior vertex preserves adjacent distinctness when the new neighbours differ. -/
set_option autoImplicit false
universe u
namespace DaggerAdjacentWordDeletions

theorem adjacentDistinct_delete {α : Type u} {d : ℕ} (f : Fin (d + 3) → α)
    (hf : ∀ k : Fin (d + 2), f k.castSucc ≠ f k.succ)
    (i : Fin (d + 1)) (hg : f i.castSucc.castSucc ≠ f i.succ.succ) :
    ∀ j : Fin (d + 1), f (i.succ.castSucc.succAbove j.castSucc) ≠
      f (i.succ.castSucc.succAbove j.succ) := by
  intro j
  obtain hj | he | hj := lt_trichotomy j i
  · have hjn : j.val < i.val := hj
    have hp : j.castSucc.castSucc < i.succ.castSucc := by
      change j.val < i.val + 1
      omega
    have hq : j.succ.castSucc < i.succ.castSucc := by
      change j.val + 1 < i.val + 1
      omega
    rw [Fin.succAbove_of_castSucc_lt _ _ hp, Fin.succAbove_of_castSucc_lt _ _ hq]
    simpa only [← Fin.succ_castSucc] using hf j.castSucc
  · subst j
    have hp : i.castSucc.castSucc < i.succ.castSucc := by
      change i.val < i.val + 1
      omega
    rw [Fin.succAbove_of_castSucc_lt _ _ hp, Fin.succAbove_of_le_castSucc _ _ le_rfl]
    exact hg
  · have hjn : i.val < j.val := hj
    have hp : i.succ.castSucc ≤ j.castSucc.castSucc := by
      change i.val + 1 ≤ j.val
      omega
    have hq : i.succ.castSucc ≤ j.succ.castSucc := by
      change i.val + 1 ≤ j.val + 1
      omega
    rw [Fin.succAbove_of_le_castSucc _ _ hp, Fin.succAbove_of_le_castSucc _ _ hq]
    simpa only [← Fin.succ_castSucc] using hf j.succ

end DaggerAdjacentWordDeletions
