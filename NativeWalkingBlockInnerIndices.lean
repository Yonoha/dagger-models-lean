import NativeWalkingWordBlocks

/-! All four actual block insertion/deletion positions are inner. -/
set_option autoImplicit false
open DaggerNativeWalkingSimplexWords DaggerNativeWalkingWordBlocks
namespace DaggerNativeWalkingBlockInnerIndices
variable {n d : ℕ} (w : Words n d) (h : ∃ i, (w.val i).2 = true)
  (hs : Function.Surjective (fun i ↦ (w.val i).1))
include hs

theorem terminal_insertion (ha : active w h < Fin.last n) :
    (lastActive w h).succ ≠ 0 ∧ (lastActive w h).succ ≠ Fin.last (d + 1) := by
  have hb := lastActive_lt_last w h hs ha
  refine ⟨Fin.succ_ne_zero _, fun he ↦ ?_⟩
  exact (Fin.ne_last_of_lt hb) (Fin.succ_inj.mp he)

theorem initial_insertion (ha : 0 < active w h) :
    (firstActive w h).castSucc ≠ 0 ∧ (firstActive w h).castSucc ≠ Fin.last (d + 1) := by
  have hb := firstActive_pos w h hs ha
  exact ⟨fun he ↦ (ne_of_gt hb) (Fin.castSucc_eq_zero_iff.mp he), Fin.castSucc_ne_last _⟩

theorem terminal_deletion (ha : active w h < Fin.last n)
    (ht : (w.val (lastActive w h)).2 = false) :
    lastActive w h ≠ 0 ∧ lastActive w h ≠ Fin.last d := by
  exact ⟨Fin.ne_zero_of_lt (firstTrue_lt_lastActive w h ht),
    Fin.ne_last_of_lt (lastActive_lt_last w h hs ha)⟩

theorem initial_deletion (ha : 0 < active w h)
    (ht : (w.val (firstActive w h)).2 = false) :
    firstActive w h ≠ 0 ∧ firstActive w h ≠ Fin.last d := by
  exact ⟨ne_of_gt (firstActive_pos w h hs ha),
    Fin.ne_last_of_lt ((firstActive_lt_firstTrue w h ht).trans_le (Fin.le_last _))⟩

end DaggerNativeWalkingBlockInnerIndices
