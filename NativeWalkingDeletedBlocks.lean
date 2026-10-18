import NativeWalkingMarkedWordOperators

/-! Deleting the false block end gives the opposite true block end at the exact inverse position. -/
set_option autoImplicit false
open DaggerNativeWalkingSimplexWords DaggerNativeWalkingWordBlocks
open DaggerNativeWalkingMarkedWordOperators
namespace DaggerNativeWalkingDeletedBlocks
noncomputable section

theorem terminal_deleted_boundary {n d : ℕ} (w : Words n (d + 1))
    (h : ∃ k, (w.val k).2 = true)
    (hnd : ∀ k : Fin (d + 1), w.val k.castSucc ≠ w.val k.succ)
    (ht : (w.val (lastActive w h)).2 = false)
    (hn : ∃ k, ((deleteWords w (lastActive w h)).val k).2 = true) :
    (lastActive (deleteWords w (lastActive w h)) hn).succ = lastActive w h ∧
      ((deleteWords w (lastActive w h)).val
        (lastActive (deleteWords w (lastActive w h)) hn)).2 = true := by
  let i := lastActive w h
  let v := deleteWords w i
  have ha : active v hn = active w h := active_delete_false w h i ht hn
  obtain ⟨q, hq⟩ := Fin.eq_succ_of_ne_zero
    (Fin.ne_zero_of_lt (firstTrue_lt_lastActive w h ht))
  have hqi : i = q.succ := hq
  have hp : firstTrue w h ≤ q.castSucc := by
    have hh := firstTrue_lt_lastActive w h ht
    rw [hq] at hh
    change (firstTrue w h).val < q.val + 1 at hh
    change (firstTrue w h).val ≤ q.val
    omega
  have hprev : (w.val q.castSucc).1 = active w h := by
    apply le_antisymm
    · have hh := w.property (show q.castSucc ≤ i by rw [hqi]; exact Fin.castSucc_le_succ q)
      change (w.val q.castSucc).1 ≤ (w.val i).1 at hh
      simpa only [i, lastActive_level] using hh
    · exact w.property hp
  have htag : (w.val q.castSucc).2 = true := by
    cases hb : (w.val q.castSucc).2
    · have he : w.val q.castSucc = w.val q.succ := by
        apply Prod.ext
        · rw [hprev, ← hq, lastActive_level]
        · rw [hb, ← hq, ht]
      exact (hnd q he).elim
    · rfl
  have hskip : i.succAbove q = q.castSucc := by
    rw [hqi, Fin.succAbove_of_castSucc_lt _ _ Fin.castSucc_lt_succ]
  have hlevel : (v.val q).1 = active v hn := by
    change (w.val (i.succAbove q)).1 = active v hn
    rw [hskip, hprev, ha]
  have hlast : lastActive v hn = q := by
    apply le_antisymm
    · let p := lastActive v hn
      change p ≤ q
      have hlev : (w.val (i.succAbove p)).1 = active w h := by
        have hh := lastActive_level v hn
        change (w.val (i.succAbove p)).1 = active v hn at hh
        rwa [ha] at hh
      have hle : i.succAbove p ≤ i := le_lastActive w h _ hlev
      have hlt : i.succAbove p < i := lt_of_le_of_ne hle (Fin.succAbove_ne i p)
      have hpc : p.castSucc < i := by
        by_contra hc
        have hc' := le_of_not_gt hc
        rw [Fin.succAbove_of_le_castSucc _ _ hc'] at hlt
        exact not_lt_of_ge (hc'.trans p.castSucc_le_succ) hlt
      rw [hqi] at hpc
      change p.val < q.val + 1 at hpc
      change p.val ≤ q.val
      omega
    · exact le_lastActive v hn q hlevel
  constructor
  · change (lastActive v hn).succ = i
    rw [hlast]
    exact hq.symm
  · change (v.val (lastActive v hn)).2 = true
    rw [hlast]
    change (w.val (i.succAbove q)).2 = true
    rw [hskip]
    exact htag

theorem initial_deleted_boundary {n d : ℕ} (w : Words n (d + 1))
    (h : ∃ k, (w.val k).2 = true)
    (hnd : ∀ k : Fin (d + 1), w.val k.castSucc ≠ w.val k.succ)
    (ht : (w.val (firstActive w h)).2 = false)
    (hn : ∃ k, ((deleteWords w (firstActive w h)).val k).2 = true) :
    (firstActive (deleteWords w (firstActive w h)) hn).castSucc = firstActive w h ∧
      ((deleteWords w (firstActive w h)).val
        (firstActive (deleteWords w (firstActive w h)) hn)).2 = true := by
  let i := firstActive w h
  let v := deleteWords w i
  have ha : active v hn = active w h := active_delete_false w h i ht hn
  obtain ⟨q, hq⟩ := Fin.eq_castSucc_of_ne_last
    (Fin.ne_last_of_lt ((firstActive_lt_firstTrue w h ht).trans_le (Fin.le_last _)))
  have hqi : i = q.castSucc := hq.symm
  have hp : q.succ ≤ firstTrue w h := by
    have hh := firstActive_lt_firstTrue w h ht
    rw [← hq] at hh
    change q.val < (firstTrue w h).val at hh
    change q.val + 1 ≤ (firstTrue w h).val
    omega
  have hnext : (w.val q.succ).1 = active w h := by
    apply le_antisymm
    · exact w.property hp
    · have hh := w.property (show i ≤ q.succ by rw [hqi]; exact Fin.castSucc_le_succ q)
      change (w.val i).1 ≤ (w.val q.succ).1 at hh
      simpa only [i, firstActive_level] using hh
  have htag : (w.val q.succ).2 = true := by
    cases hb : (w.val q.succ).2
    · have he : w.val q.castSucc = w.val q.succ := by
        apply Prod.ext
        · rw [hq, firstActive_level, hnext]
        · rw [hq, ht, hb]
      exact (hnd q he).elim
    · rfl
  have hskip : i.succAbove q = q.succ := by rw [hqi, Fin.succAbove_castSucc_self]
  have hlevel : (v.val q).1 = active v hn := by
    change (w.val (i.succAbove q)).1 = active v hn
    rw [hskip, hnext, ha]
  have hfirst : firstActive v hn = q := by
    apply le_antisymm
    · exact firstActive_le v hn q hlevel
    · let p := firstActive v hn
      change q ≤ p
      have hlev : (w.val (i.succAbove p)).1 = active w h := by
        have hh := firstActive_level v hn
        change (w.val (i.succAbove p)).1 = active v hn at hh
        rwa [ha] at hh
      have hle : i ≤ i.succAbove p := firstActive_le w h _ hlev
      by_contra hpq
      have hpq' : p < q := lt_of_not_ge hpq
      have hpi : p.castSucc < i := by
        rw [hqi]
        simpa only [Fin.castSucc_lt_castSucc_iff] using hpq'
      rw [Fin.succAbove_of_castSucc_lt _ _ hpi] at hle
      exact not_le_of_gt hpi hle
  constructor
  · change (firstActive v hn).castSucc = i
    rw [hfirst]
    exact hq
  · change (v.val (firstActive v hn)).2 = true
    rw [hfirst]
    change (w.val (i.succAbove q)).2 = true
    rw [hskip]
    exact htag

end
end DaggerNativeWalkingDeletedBlocks
