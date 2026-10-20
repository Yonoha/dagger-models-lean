import NativeWalkingMarkedWordOperators

/-! Inserting false at a block end preserves the marked level and becomes that exact end. -/
set_option autoImplicit false
open DaggerNativeWalkingSimplexWords DaggerNativeWalkingWordInsertions
open DaggerNativeWalkingWordBlocks DaggerNativeWalkingMarkedWordOperators
namespace DaggerNativeWalkingInsertedBlocks
noncomputable section

theorem lastActive_insert_terminal {n d : ℕ} (w : Words n d)
    (h : ∃ k, (w.val k).2 = true)
    (hm : Monotone (fun k ↦
      (Fin.insert w.val (lastActive w h).succ (active w h, false) k).1))
    (hn : ∃ k, ((insertWords w (lastActive w h).succ (active w h, false) hm).val k).2 = true) :
    lastActive (insertWords w (lastActive w h).succ (active w h, false) hm) hn =
      (lastActive w h).succ := by
  let i := (lastActive w h).succ
  let v := insertWords w i (active w h, false) hm
  have ha : active v hn = active w h := active_insert_false w h i _ hm hn
  have hl : (v.val i).1 = active v hn := by rw [insertWords_new, ha]
  apply le_antisymm
  · let p := lastActive v hn
    change p ≤ i
    obtain hp | ⟨k, hk⟩ := i.eq_self_or_eq_succAbove p
    · rw [hp]
    · have hlev : (w.val k).1 = active w h := by
        have hh := lastActive_level v hn
        change (v.val p).1 = active v hn at hh
        rw [hk, insertWords_old, ha] at hh
        exact hh
      have hkq := le_lastActive w h k hlev
      have hki : k.castSucc < i := by
        change k.castSucc < (lastActive w h).succ
        simpa only [Fin.castSucc_lt_succ_iff] using hkq
      rw [hk, Fin.succAbove_of_castSucc_lt _ _ hki]
      exact hki.le
  · exact le_lastActive v hn i hl

theorem firstActive_insert_initial {n d : ℕ} (w : Words n d)
    (h : ∃ k, (w.val k).2 = true)
    (hm : Monotone (fun k ↦
      (Fin.insert w.val (firstActive w h).castSucc (active w h, false) k).1))
    (hn : ∃ k, ((insertWords w (firstActive w h).castSucc
      (active w h, false) hm).val k).2 = true) :
    firstActive (insertWords w (firstActive w h).castSucc (active w h, false) hm) hn =
      (firstActive w h).castSucc := by
  let i := (firstActive w h).castSucc
  let v := insertWords w i (active w h, false) hm
  have ha : active v hn = active w h := active_insert_false w h i _ hm hn
  have hl : (v.val i).1 = active v hn := by rw [insertWords_new, ha]
  apply le_antisymm
  · exact firstActive_le v hn i hl
  · let p := firstActive v hn
    change i ≤ p
    obtain hp | ⟨k, hk⟩ := i.eq_self_or_eq_succAbove p
    · rw [hp]
    · have hlev : (w.val k).1 = active w h := by
        have hh := firstActive_level v hn
        change (v.val p).1 = active v hn at hh
        rw [hk, insertWords_old, ha] at hh
        exact hh
      have hqk := firstActive_le w h k hlev
      have hik : i ≤ k.castSucc := by
        change (firstActive w h).castSucc ≤ k.castSucc
        simpa only [Fin.castSucc_le_castSucc_iff] using hqk
      rw [hk, Fin.succAbove_of_le_castSucc _ _ hik]
      exact hik.trans k.castSucc_le_succ

end
end DaggerNativeWalkingInsertedBlocks
