import NativeWalkingMarkedWordOperators

/-! A retained block end stays the block end if an arbitrary deletion preserves the marked level. -/
set_option autoImplicit false
open DaggerNativeWalkingSimplexWords DaggerNativeWalkingWordBlocks
open DaggerNativeWalkingMarkedWordOperators
namespace DaggerNativeWalkingRetainedBlockEnds
noncomputable section

theorem active_le_delete {n d : ℕ} (w : Words n (d + 1)) (h : ∃ k, (w.val k).2 = true)
    (i : Fin (d + 2)) (hn : ∃ k, ((deleteWords w i).val k).2 = true) :
    active w h ≤ active (deleteWords w i) hn :=
  active_le_true w h (i.succAbove (firstTrue (deleteWords w i) hn))
    (firstTrue_tag (deleteWords w i) hn)

theorem retained_terminal {n d : ℕ} (w : Words n (d + 1)) (h : ∃ k, (w.val k).2 = true)
    (i : Fin (d + 2)) (hi : i ≠ lastActive w h)
    (hn : ∃ k, ((deleteWords w i).val k).2 = true)
    (ha : active (deleteWords w i) hn = active w h) :
    i.succAbove (lastActive (deleteWords w i) hn) = lastActive w h ∧
      ((deleteWords w i).val (lastActive (deleteWords w i) hn)).2 =
        (w.val (lastActive w h)).2 := by
  let v := deleteWords w i
  obtain he | ⟨q, hq⟩ := i.eq_self_or_eq_succAbove (lastActive w h)
  · exact (hi he.symm).elim
  · have hlevel : (v.val q).1 = active v hn := by
      change (w.val (i.succAbove q)).1 = active v hn
      rw [← hq, lastActive_level, ha]
    have hlast : lastActive v hn = q := by
      apply le_antisymm
      · have hp : (w.val (i.succAbove (lastActive v hn))).1 = active w h :=
          (lastActive_level v hn).trans ha
        have hh := le_lastActive w h _ hp
        rw [hq] at hh
        exact (Fin.succAboveOrderEmb i).le_iff_le.mp hh
      · exact le_lastActive v hn q hlevel
    have heq : i.succAbove (lastActive v hn) = lastActive w h := by
      rw [hlast]
      exact hq.symm
    exact ⟨heq, congrArg (fun k ↦ (w.val k).2) heq⟩

theorem retained_initial {n d : ℕ} (w : Words n (d + 1)) (h : ∃ k, (w.val k).2 = true)
    (i : Fin (d + 2)) (hi : i ≠ firstActive w h)
    (hn : ∃ k, ((deleteWords w i).val k).2 = true)
    (ha : active (deleteWords w i) hn = active w h) :
    i.succAbove (firstActive (deleteWords w i) hn) = firstActive w h ∧
      ((deleteWords w i).val (firstActive (deleteWords w i) hn)).2 =
        (w.val (firstActive w h)).2 := by
  let v := deleteWords w i
  obtain he | ⟨q, hq⟩ := i.eq_self_or_eq_succAbove (firstActive w h)
  · exact (hi he.symm).elim
  · have hlevel : (v.val q).1 = active v hn := by
      change (w.val (i.succAbove q)).1 = active v hn
      rw [← hq, firstActive_level, ha]
    have hfirst : firstActive v hn = q := by
      apply le_antisymm
      · exact firstActive_le v hn q hlevel
      · have hp : (w.val (i.succAbove (firstActive v hn))).1 = active w h :=
          (firstActive_level v hn).trans ha
        have hh := firstActive_le w h _ hp
        rw [hq] at hh
        exact (Fin.succAboveOrderEmb i).le_iff_le.mp hh
    have heq : i.succAbove (firstActive v hn) = firstActive w h := by
      rw [hfirst]
      exact hq.symm
    exact ⟨heq, congrArg (fun k ↦ (w.val k).2) heq⟩

end
end DaggerNativeWalkingRetainedBlockEnds
