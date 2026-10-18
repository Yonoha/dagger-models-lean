import NativeWalkingWordBlocks

/-! The two actual block gaps and their verified neighbouring vertices. -/
set_option autoImplicit false
open DaggerNativeWalkingSimplexWords DaggerNativeWalkingWordBlocks
namespace DaggerNativeWalkingBlockSlots
noncomputable section
variable {n d : ℕ} (w : Words n (d + 1)) (h : ∃ i, (w.val i).2 = true)
  (hs : Function.Surjective (fun i ↦ (w.val i).1))

theorem active_lt_after_last (i : Fin (d + 2)) (hi : lastActive w h < i) :
    active w h < (w.val i).1 := by
  have hm := w.property hi.le
  change (w.val (lastActive w h)).1 ≤ (w.val i).1 at hm
  rw [lastActive_level] at hm
  apply lt_of_le_of_ne hm
  intro he
  exact not_le_of_gt hi (le_lastActive w h i he.symm)

theorem before_first_lt_active (i : Fin (d + 2)) (hi : i < firstActive w h) :
    (w.val i).1 < active w h := by
  have hm := w.property hi.le
  change (w.val i).1 ≤ (w.val (firstActive w h)).1 at hm
  rw [firstActive_level] at hm
  apply lt_of_le_of_ne hm
  intro he
  exact not_le_of_gt hi (firstActive_le w h i he)

def terminalSlot (ha : active w h < Fin.last n) : Fin (d + 1) :=
  (lastActive w h).castPred (Fin.ne_last_of_lt (lastActive_lt_last w h hs ha))

theorem terminalSlot_castSucc (ha : active w h < Fin.last n) :
    (terminalSlot w h hs ha).castSucc = lastActive w h := Fin.castSucc_castPred _ _

def initialSlot (ha : 0 < active w h) : Fin (d + 1) :=
  (firstActive w h).pred (ne_of_gt (firstActive_pos w h hs ha))

theorem initialSlot_succ (ha : 0 < active w h) :
    (initialSlot w h hs ha).succ = firstActive w h := Fin.succ_pred _ _

theorem terminal_left_le (ha : active w h < Fin.last n) :
    (w.val (terminalSlot w h hs ha).castSucc).1 ≤ active w h := by
  rw [terminalSlot_castSucc, lastActive_level]

theorem terminal_right_le (ha : active w h < Fin.last n) :
    active w h ≤ (w.val (terminalSlot w h hs ha).succ).1 := by
  have hh := active_lt_after_last w h (terminalSlot w h hs ha).succ (by
    rw [← terminalSlot_castSucc w h hs ha]
    exact Fin.castSucc_lt_succ)
  exact hh.le

theorem initial_left_le (ha : 0 < active w h) :
    (w.val (initialSlot w h hs ha).castSucc).1 ≤ active w h := by
  have hh := before_first_lt_active w h (initialSlot w h hs ha).castSucc (by
    rw [← initialSlot_succ w h hs ha]
    exact Fin.castSucc_lt_succ)
  exact hh.le

theorem initial_right_le (ha : 0 < active w h) :
    active w h ≤ (w.val (initialSlot w h hs ha).succ).1 := by
  rw [initialSlot_succ, firstActive_level]

theorem terminal_neighbors_ne (ha : active w h < Fin.last n)
    (ht : (w.val (lastActive w h)).2 = true) :
    w.val (terminalSlot w h hs ha).castSucc ≠ (active w h, false) ∧
      (active w h, false) ≠ w.val (terminalSlot w h hs ha).succ := by
  constructor
  · intro he
    have hb := congrArg Prod.snd he
    change (w.val (terminalSlot w h hs ha).castSucc).2 = false at hb
    rw [terminalSlot_castSucc, ht] at hb
    exact Bool.false_ne_true hb.symm
  · intro he
    have hh := active_lt_after_last w h (terminalSlot w h hs ha).succ (by
      rw [← terminalSlot_castSucc w h hs ha]
      exact Fin.castSucc_lt_succ)
    have he' := congrArg Prod.fst he
    exact hh.ne he'

theorem initial_neighbors_ne (ha : 0 < active w h)
    (ht : (w.val (firstActive w h)).2 = true) :
    w.val (initialSlot w h hs ha).castSucc ≠ (active w h, false) ∧
      (active w h, false) ≠ w.val (initialSlot w h hs ha).succ := by
  constructor
  · intro he
    have hh := before_first_lt_active w h (initialSlot w h hs ha).castSucc (by
      rw [← initialSlot_succ w h hs ha]
      exact Fin.castSucc_lt_succ)
    have he' := congrArg Prod.fst he
    exact hh.ne he'
  · intro he
    have hb := congrArg Prod.snd he
    change false = (w.val (initialSlot w h hs ha).succ).2 at hb
    rw [initialSlot_succ, ht] at hb
    exact Bool.false_ne_true hb

end
end DaggerNativeWalkingBlockSlots
