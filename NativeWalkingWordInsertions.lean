import NativeWalkingWordBlocks
import TopCatModelCategory.Fin

/-! Exact insertion operators into the original walking-interval product. -/
set_option autoImplicit false
open CategoryTheory Simplicial MonoidalCategory
open DaggerActualFreeWalkingIsoIntegerObstruction DaggerNativeWalkingSimplexWords
open DaggerNativeWalkingWordFaces
universe u
namespace DaggerNativeWalkingWordInsertions
noncomputable section

lemma fst_insert {n d : ℕ} (w : Words n d) (i : Fin (d + 2)) (v : Fin (n + 1) × Bool) :
    (fun k ↦ (Fin.insert w.val i v k).1) = Fin.insert (fun k ↦ (w.val k).1) i v.1 := by
  funext k
  obtain rfl | ⟨k, rfl⟩ := i.eq_self_or_eq_succAbove k
  · simp
  · simp

def insertWords {n d : ℕ} (w : Words n d) (i : Fin (d + 2)) (v : Fin (n + 1) × Bool)
    (hm : Monotone (fun k ↦ (Fin.insert w.val i v k).1)) : Words n (d + 1) :=
  ⟨Fin.insert w.val i v, hm⟩

def insertBetween {n d : ℕ} (w : Words n (d + 1)) (i : Fin (d + 1))
    (v : Fin (n + 1) × Bool) (hl : (w.val i.castSucc).1 ≤ v.1)
    (hr : v.1 ≤ (w.val i.succ).1) : Words n (d + 2) :=
  insertWords w i.succ.castSucc v (by
    rw [fst_insert]
    exact Fin.monotone_insert ⟨fun k ↦ (w.val k).1, w.property⟩ i v.1 hl hr)

theorem insertWords_old {n d : ℕ} (w : Words n d) (i : Fin (d + 2))
    (v : Fin (n + 1) × Bool) (hm : Monotone (fun k ↦ (Fin.insert w.val i v k).1))
    (j : Fin (d + 1)) : (insertWords w i v hm).val (i.succAbove j) = w.val j :=
  Fin.insert_apply_succAbove w.val i v j

theorem insertWords_new {n d : ℕ} (w : Words n d) (i : Fin (d + 2))
    (v : Fin (n + 1) × Bool) (hm : Monotone (fun k ↦ (Fin.insert w.val i v k).1)) :
    (insertWords w i v hm).val i = v := Fin.insert_self w.val i v

theorem insertWords_surjective {n d : ℕ} (w : Words n d) (i : Fin (d + 2))
    (v : Fin (n + 1) × Bool) (hm : Monotone (fun k ↦ (Fin.insert w.val i v k).1))
    (hs : Function.Surjective (fun k ↦ (w.val k).1)) :
    Function.Surjective (fun k ↦ ((insertWords w i v hm).val k).1) := by
  intro j
  obtain ⟨k, hk⟩ := hs j
  dsimp only at hk
  refine ⟨i.succAbove k, ?_⟩
  change ((insertWords w i v hm).val (i.succAbove k)).1 = j
  rw [insertWords_old, hk]

theorem insertWords_true {n d : ℕ} (w : Words n d) (i : Fin (d + 2))
    (v : Fin (n + 1) × Bool) (hm : Monotone (fun k ↦ (Fin.insert w.val i v k).1))
    (ht : ∃ k, (w.val k).2 = true) : ∃ k, ((insertWords w i v hm).val k).2 = true := by
  obtain ⟨k, hk⟩ := ht
  exact ⟨i.succAbove k, by rw [insertWords_old, hk]⟩

theorem delta_insertWords {n d : ℕ} (w : Words n d) (i : Fin (d + 2))
    (v : Fin (n + 1) × Bool) (hm : Monotone (fun k ↦ (Fin.insert w.val i v k).1)) :
    (Δ[n] ⊗ J.{u}).δ i (ofWords.{u} (insertWords w i v hm)) = ofWords.{u} w := by
  apply (wordEquiv.{u} n d).injective
  apply Subtype.ext
  funext k
  change (coordinates ((Δ[n] ⊗ J.{u}).δ i (ofWords.{u} (insertWords w i v hm)))).val k =
    (coordinates (ofWords.{u} w)).val k
  rw [coordinates_delta, coordinates_ofWords, coordinates_ofWords, insertWords_old]

theorem insertWords_notMem {n d : ℕ} (w : Words n d) (i : Fin (d + 2))
    (v : Fin (n + 1) × Bool) (hm : Monotone (fun k ↦ (Fin.insert w.val i v k).1))
    (hs : Function.Surjective (fun k ↦ (w.val k).1)) (ht : ∃ k, (w.val k).2 = true) :
    ofWords.{u} (insertWords w i v hm) ∉
      ((SSet.boundary n).unionProd
        DaggerNativeWalkingRelativeGenerators.zeroSubcomplex.{u}).obj _ := by
  rw [notMem_relative_iff, coordinates_ofWords]
  exact ⟨insertWords_surjective w i v hm hs, insertWords_true w i v hm ht⟩

end
end DaggerNativeWalkingWordInsertions
