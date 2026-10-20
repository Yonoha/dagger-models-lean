import NativeWalkingWordInsertions
import NativeWalkingWordBlocks

/-! Exact deletion and preservation of the first marked level under false-vertex operations. -/
set_option autoImplicit false
open CategoryTheory Simplicial MonoidalCategory
open DaggerActualFreeWalkingIsoIntegerObstruction DaggerNativeWalkingSimplexWords
open DaggerNativeWalkingWordInsertions DaggerNativeWalkingWordBlocks
universe u
namespace DaggerNativeWalkingMarkedWordOperators
noncomputable section

def deleteWords {n d : ℕ} (w : Words n (d + 1)) (i : Fin (d + 2)) : Words n d :=
  ⟨fun k ↦ w.val (i.succAbove k), w.property.comp (Fin.succAboveOrderEmb i).monotone⟩

theorem deleteWords_ofWords {n d : ℕ} (w : Words n (d + 1)) (i : Fin (d + 2)) :
    ofWords.{u} (deleteWords w i) = (Δ[n] ⊗ J.{u}).δ i (ofWords.{u} w) := by
  apply (wordEquiv.{u} n d).injective
  apply Subtype.ext
  funext k
  change (coordinates (ofWords.{u} (deleteWords w i))).val k =
    (coordinates ((Δ[n] ⊗ J.{u}).δ i (ofWords.{u} w))).val k
  rw [DaggerNativeWalkingWordFaces.coordinates_delta, coordinates_ofWords, coordinates_ofWords]
  rfl

theorem deleteWords_true {n d : ℕ} (w : Words n (d + 1)) (i : Fin (d + 2))
    (hi : (w.val i).2 = false) (ht : ∃ k, (w.val k).2 = true) :
    ∃ k, ((deleteWords w i).val k).2 = true := by
  obtain ⟨k, hk⟩ := ht
  obtain rfl | ⟨k, rfl⟩ := i.eq_self_or_eq_succAbove k
  · rw [hi] at hk
    exact (Bool.false_ne_true hk).elim
  · exact ⟨k, hk⟩

theorem deleteWords_surjective {n d : ℕ} (w : Words n (d + 1)) (i : Fin (d + 2))
    (hs : Function.Surjective (fun k ↦ (w.val k).1))
    (hr : ∃ k, k ≠ i ∧ (w.val k).1 = (w.val i).1) :
    Function.Surjective (fun k ↦ ((deleteWords w i).val k).1) := by
  intro a
  obtain ⟨k, hk⟩ := hs a
  obtain he | ⟨k', he⟩ := i.eq_self_or_eq_succAbove k
  · obtain ⟨r, hri, hre⟩ := hr
    obtain he' | ⟨r', he'⟩ := i.eq_self_or_eq_succAbove r
    · exact (hri he').elim
    · refine ⟨r', ?_⟩
      change (w.val (i.succAbove r')).1 = a
      rw [← he', hre, ← he]
      exact hk
  · refine ⟨k', ?_⟩
    change (w.val (i.succAbove k')).1 = a
    rw [← he]
    exact hk

theorem active_insert_false {n d : ℕ} (w : Words n d) (h : ∃ k, (w.val k).2 = true)
    (i : Fin (d + 2)) (a : Fin (n + 1))
    (hm : Monotone (fun k ↦ (Fin.insert w.val i (a, false) k).1))
    (hn : ∃ k, ((insertWords w i (a, false) hm).val k).2 = true) :
    active (insertWords w i (a, false) hm) hn = active w h := by
  let v := insertWords w i (a, false) hm
  apply le_antisymm
  · have ht : (v.val (i.succAbove (firstTrue w h))).2 = true := by
      rw [insertWords_old]
      exact firstTrue_tag w h
    have hh := active_le_true v hn _ ht
    simpa only [v, insertWords_old] using hh
  · let p := firstTrue v hn
    have ht : (v.val p).2 = true := firstTrue_tag v hn
    change active w h ≤ (v.val p).1
    obtain hp | ⟨k, hk⟩ := i.eq_self_or_eq_succAbove p
    · rw [hp, insertWords_new] at ht
      exact (Bool.false_ne_true ht).elim
    · rw [hk, insertWords_old] at ht ⊢
      exact active_le_true w h k ht

theorem active_delete_false {n d : ℕ} (w : Words n (d + 1))
    (h : ∃ k, (w.val k).2 = true) (i : Fin (d + 2)) (hi : (w.val i).2 = false)
    (hn : ∃ k, ((deleteWords w i).val k).2 = true) :
    active (deleteWords w i) hn = active w h := by
  apply le_antisymm
  · obtain hp | ⟨k, hk⟩ := i.eq_self_or_eq_succAbove (firstTrue w h)
    · have ht := firstTrue_tag w h
      rw [hp, hi] at ht
      exact (Bool.false_ne_true ht).elim
    · have ht : ((deleteWords w i).val k).2 = true := by
        change (w.val (i.succAbove k)).2 = true
        rw [← hk]
        exact firstTrue_tag w h
      have hh := active_le_true (deleteWords w i) hn k ht
      change active (deleteWords w i) hn ≤ (w.val (i.succAbove k)).1 at hh
      simpa only [← hk] using hh
  · exact active_le_true w h (i.succAbove (firstTrue (deleteWords w i) hn))
      (firstTrue_tag (deleteWords w i) hn)

end
end DaggerNativeWalkingMarkedWordOperators
