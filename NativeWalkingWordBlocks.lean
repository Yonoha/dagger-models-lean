import NativeWalkingWordFaces

/-!
# The first marked level and its whole block in exact walking-interval words

All indices refer to the original all-dimensional vertex word. These bounds
supply inner insertion/deletion positions; they do not assert a pairing yet.
-/
set_option autoImplicit false
open CategoryTheory Simplicial MonoidalCategory
open DaggerNativeWalkingSimplexWords
universe u
namespace DaggerNativeWalkingWordBlocks
noncomputable section
variable {n d : ℕ} (w : Words n d) (h : ∃ i, (w.val i).2 = true)

noncomputable def trueIndices : Finset (Fin (d + 1)) :=
  Finset.univ.filter (fun i ↦ (w.val i).2 = true)

include h in
theorem trueIndices_nonempty : (trueIndices w).Nonempty := by
  obtain ⟨i, hi⟩ := h
  exact ⟨i, by simp [trueIndices, hi]⟩

noncomputable def firstTrue : Fin (d + 1) :=
  (trueIndices w).min' (trueIndices_nonempty w h)

theorem firstTrue_tag : (w.val (firstTrue w h)).2 = true := by
  simpa [trueIndices] using (trueIndices w).min'_mem (trueIndices_nonempty w h)

theorem firstTrue_le (i : Fin (d + 1)) (hi : (w.val i).2 = true) :
    firstTrue w h ≤ i :=
  (trueIndices w).min'_le i (by simp [trueIndices, hi])

noncomputable def active : Fin (n + 1) := (w.val (firstTrue w h)).1

theorem active_le_true (i : Fin (d + 1)) (hi : (w.val i).2 = true) :
    active w h ≤ (w.val i).1 := w.property (firstTrue_le w h i hi)

theorem false_below_active (i : Fin (d + 1)) (hi : (w.val i).1 < active w h) :
    (w.val i).2 = false := by
  cases hb : (w.val i).2
  · rfl
  · exact (not_le_of_gt hi (active_le_true w h i hb)).elim

noncomputable def activeIndices : Finset (Fin (d + 1)) :=
  Finset.univ.filter (fun i ↦ (w.val i).1 = active w h)

theorem activeIndices_nonempty : (activeIndices w h).Nonempty :=
  ⟨firstTrue w h, by simp [activeIndices, active]⟩

noncomputable def firstActive : Fin (d + 1) :=
  (activeIndices w h).min' (activeIndices_nonempty w h)

noncomputable def lastActive : Fin (d + 1) :=
  (activeIndices w h).max' (activeIndices_nonempty w h)

theorem firstActive_level : (w.val (firstActive w h)).1 = active w h := by
  simpa [activeIndices] using (activeIndices w h).min'_mem (activeIndices_nonempty w h)

theorem lastActive_level : (w.val (lastActive w h)).1 = active w h := by
  simpa [activeIndices] using (activeIndices w h).max'_mem (activeIndices_nonempty w h)

theorem firstActive_le (i : Fin (d + 1)) (hi : (w.val i).1 = active w h) :
    firstActive w h ≤ i :=
  (activeIndices w h).min'_le i (by simp [activeIndices, hi])

theorem le_lastActive (i : Fin (d + 1)) (hi : (w.val i).1 = active w h) :
    i ≤ lastActive w h :=
  (activeIndices w h).le_max' i (by simp [activeIndices, hi])

theorem firstActive_le_firstTrue : firstActive w h ≤ firstTrue w h :=
  firstActive_le w h _ rfl

theorem firstTrue_le_lastActive : firstTrue w h ≤ lastActive w h :=
  le_lastActive w h _ rfl

theorem lastActive_lt_last (hs : Function.Surjective (fun i ↦ (w.val i).1))
    (ha : active w h < Fin.last n) : lastActive w h < Fin.last d := by
  obtain ⟨i, hi⟩ := hs (Fin.last n)
  have hli : lastActive w h < i := by
    by_contra hli
    have hm := w.property (le_of_not_gt hli)
    dsimp only at hm hi
    rw [hi, lastActive_level] at hm
    exact not_le_of_gt ha hm
  exact hli.trans_le (Fin.le_last i)

theorem firstActive_pos (hs : Function.Surjective (fun i ↦ (w.val i).1))
    (ha : 0 < active w h) : 0 < firstActive w h := by
  obtain ⟨i, hi⟩ := hs 0
  have hli : i < firstActive w h := by
    by_contra hli
    have hm := w.property (le_of_not_gt hli)
    dsimp only at hm hi
    rw [hi, firstActive_level] at hm
    exact not_le_of_gt ha hm
  exact lt_of_le_of_lt i.zero_le hli

theorem firstTrue_lt_lastActive (ht : (w.val (lastActive w h)).2 = false) :
    firstTrue w h < lastActive w h := by
  apply lt_of_le_of_ne (firstTrue_le_lastActive w h)
  intro he
  have htag := firstTrue_tag w h
  rw [he, ht] at htag
  exact Bool.false_ne_true htag

theorem firstActive_lt_firstTrue (ht : (w.val (firstActive w h)).2 = false) :
    firstActive w h < firstTrue w h := by
  apply lt_of_le_of_ne (firstActive_le_firstTrue w h)
  intro he
  have htag := firstTrue_tag w h
  rw [← he, ht] at htag
  exact Bool.false_ne_true htag

end
end DaggerNativeWalkingWordBlocks
