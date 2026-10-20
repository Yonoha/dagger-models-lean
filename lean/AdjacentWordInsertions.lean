import TopCatModelCategory.Fin

/-! Inserting a vertex distinct from its two neighbours preserves adjacent distinctness. -/
set_option autoImplicit false
universe u
namespace DaggerAdjacentWordInsertions

lemma adjacentDistinct_insert {α : Type u} {d : ℕ} (f : Fin (d + 2) → α)
    (hf : ∀ k : Fin (d + 1), f k.castSucc ≠ f k.succ)
    (i : Fin (d + 1)) (v : α) (hl : f i.castSucc ≠ v) (hr : v ≠ f i.succ) :
    ∀ j : Fin (d + 2),
      Fin.insert f i.succ.castSucc v j.castSucc ≠ Fin.insert f i.succ.castSucc v j.succ := by
  intro j
  by_cases hjl : j = i.castSucc
  · subst hjl
    simpa [← Fin.succ_castSucc,
      Fin.insert_apply f i.castSucc v i.castSucc.castSucc (by simp [Fin.ext_iff])] using hl
  by_cases hjr : j = i.succ
  · subst hjr
    simpa [← Fin.succ_castSucc,
      Fin.insert_apply f i.castSucc v i.succ.succ (by simp [Fin.ext_iff]),
      Fin.predAbove_of_succ_le i.castSucc i.succ.succ (by
          simp only [Fin.le_def, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ] at *
          omega)] using hr
  have h₁ : j.castSucc ≠ i.castSucc.succ := by
    intro he
    have hv := congrArg Fin.val he
    apply hjr
    apply Fin.ext
    simpa using hv
  have h₂ : j.succ ≠ i.castSucc.succ := by simpa using hjl
  rw [← Fin.succ_castSucc, Fin.insert_apply f i.castSucc v j.castSucc h₁,
    Fin.insert_apply f i.castSucc v j.succ h₂]
  let a := i.castSucc.predAbove j.castSucc
  let b := i.castSucc.predAbove j.succ
  have hab : (a : ℕ) + 1 = b := by
    dsimp [a, b]
    by_cases hj : j ≤ i.castSucc
    · rw [Fin.predAbove_of_le_castSucc _ _ (by
          simp only [Fin.le_def, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ] at *
          omega),
        Fin.predAbove_of_le_castSucc _ _ (by
          simp only [Fin.le_def, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ] at *
          omega)]
      rfl
    · obtain ⟨j, rfl⟩ := Fin.eq_succ_of_ne_zero (show j ≠ 0 by intro he; subst he; simp at hj)
      rw [Fin.predAbove_of_castSucc_lt _ _ (by
          simp only [Fin.le_def, Fin.lt_def, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ] at *
          omega),
        Fin.predAbove_of_castSucc_lt _ _ (by
          simp only [Fin.le_def, Fin.lt_def, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ] at *
          omega)]
      simp only [← Fin.succ_castSucc, Fin.pred_succ]
      rfl
  let k : Fin (d + 1) := ⟨a.val, by have := b.isLt; omega⟩
  have ha : a = k.castSucc := by apply Fin.ext; rfl
  have hb : b = k.succ := by apply Fin.ext; exact hab.symm
  change f a ≠ f b
  rw [ha, hb]
  exact hf k

end DaggerAdjacentWordInsertions
