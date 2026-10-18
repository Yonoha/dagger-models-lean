import NativeWalkingBlockSlots

/-! The new neighbours at both false block-end deletions have different projection levels. -/
set_option autoImplicit false
open DaggerNativeWalkingSimplexWords DaggerNativeWalkingWordBlocks DaggerNativeWalkingBlockSlots
namespace DaggerNativeWalkingBlockDeletionGaps
noncomputable section

theorem terminal_gap {n d : ℕ} (w : Words n (d + 2)) (h : ∃ k, (w.val k).2 = true)
    (ht : (w.val (lastActive w h)).2 = false) (i : Fin (d + 1))
    (hi : i.succ.castSucc = lastActive w h) :
    w.val i.castSucc.castSucc ≠ w.val i.succ.succ := by
  have hp : firstTrue w h ≤ i.castSucc.castSucc := by
    have hh := firstTrue_lt_lastActive w h ht
    rw [← hi] at hh
    change (firstTrue w h).val < i.val + 1 at hh
    change (firstTrue w h).val ≤ i.val
    omega
  have hprev : (w.val i.castSucc.castSucc).1 = active w h := by
    apply le_antisymm
    · have hh := w.property
        (show i.castSucc.castSucc ≤ lastActive w h by
          rw [← hi]
          change i.val ≤ i.val + 1
          omega)
      change (w.val i.castSucc.castSucc).1 ≤ (w.val (lastActive w h)).1 at hh
      rwa [lastActive_level] at hh
    · exact w.property hp
  have hnext := active_lt_after_last w h i.succ.succ (by
    rw [← hi]
    exact Fin.castSucc_lt_succ)
  intro he
  have he' := congrArg Prod.fst he
  rw [hprev] at he'
  exact hnext.ne he'

theorem initial_gap {n d : ℕ} (w : Words n (d + 2)) (h : ∃ k, (w.val k).2 = true)
    (ht : (w.val (firstActive w h)).2 = false) (i : Fin (d + 1))
    (hi : i.succ.castSucc = firstActive w h) :
    w.val i.castSucc.castSucc ≠ w.val i.succ.succ := by
  have hp : i.succ.succ ≤ firstTrue w h := by
    have hh := firstActive_lt_firstTrue w h ht
    rw [← hi] at hh
    change i.val + 1 < (firstTrue w h).val at hh
    change i.val + 2 ≤ (firstTrue w h).val
    omega
  have hnext : (w.val i.succ.succ).1 = active w h := by
    apply le_antisymm
    · exact w.property hp
    · have hh := w.property
        (show firstActive w h ≤ i.succ.succ by rw [← hi]; exact Fin.castSucc_le_succ i.succ)
      change (w.val (firstActive w h)).1 ≤ (w.val i.succ.succ).1 at hh
      rwa [firstActive_level] at hh
  have hprev := before_first_lt_active w h i.castSucc.castSucc (by
    rw [← hi]
    change i.val < i.val + 1
    omega)
  intro he
  have he' := congrArg Prod.fst he
  rw [hnext] at he'
  exact hprev.ne he'

end
end DaggerNativeWalkingBlockDeletionGaps
