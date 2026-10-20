import NativeWalkingDeletedBlocks
import NativeWalkingBlockDeletionGaps
import NativeWalkingBlockInnerIndices
import AdjacentWordDeletions

/-! Both upper block branches delete to genuine relative nondegenerate lower simplices. -/
set_option autoImplicit false
open CategoryTheory Simplicial MonoidalCategory
open DaggerActualFreeWalkingIsoIntegerObstruction DaggerNativeWalkingSimplexWords
open DaggerNativeWalkingWordFaces DaggerNativeWalkingWordBlocks
open DaggerNativeWalkingMarkedWordOperators DaggerNativeWalkingDeletedBlocks
open DaggerNativeWalkingBlockDeletionGaps DaggerNativeWalkingBlockInnerIndices
universe u
namespace DaggerNativeWalkingBlockUpperDeletions
noncomputable section

theorem exists_innerSlot {d : ℕ} (i : Fin (d + 3)) (h0 : i ≠ 0)
    (hl : i ≠ Fin.last (d + 2)) : ∃ p : Fin (d + 1), p.succ.castSucc = i := by
  obtain ⟨q, hq⟩ := Fin.eq_castSucc_of_ne_last hl
  have hq0 : q ≠ 0 := by
    intro he
    apply h0
    rw [← hq, he]
    rfl
  obtain ⟨p, hp⟩ := Fin.eq_succ_of_ne_zero hq0
  refine ⟨p, ?_⟩
  rw [← hp]
  exact hq

theorem delta_inner_nonDegenerate {n d : ℕ} (x : (Δ[n] ⊗ J.{u} : SSet.{u}) _⦋d + 2⦌)
    (hx : x ∈ (Δ[n] ⊗ J.{u}).nonDegenerate (d + 2)) (p : Fin (d + 1))
    (hg : (coordinates x).val p.castSucc.castSucc ≠ (coordinates x).val p.succ.succ) :
    (Δ[n] ⊗ J.{u}).δ p.succ.castSucc x ∈ (Δ[n] ⊗ J.{u}).nonDegenerate (d + 1) := by
  apply (nonDegenerate_iff _).mpr
  intro j
  rw [coordinates_delta, coordinates_delta]
  exact DaggerAdjacentWordDeletions.adjacentDistinct_delete (coordinates x).val
    ((nonDegenerate_iff x).mp hx) p hg j

variable {n d : ℕ} (x : (Δ[n] ⊗ J.{u} : SSet.{u}) _⦋d + 2⦌)
  (h : ∃ k, ((coordinates x).val k).2 = true)

def terminalLower : (Δ[n] ⊗ J.{u} : SSet.{u}) _⦋d + 1⦌ :=
  (Δ[n] ⊗ J.{u}).δ (lastActive (coordinates x) h) x

def initialLower : (Δ[n] ⊗ J.{u} : SSet.{u}) _⦋d + 1⦌ :=
  (Δ[n] ⊗ J.{u}).δ (firstActive (coordinates x) h) x

theorem terminalLower_relative
    (hs : Function.Surjective (fun k ↦ ((coordinates x).val k).1))
    (ht : ((coordinates x).val (lastActive (coordinates x) h)).2 = false) :
    terminalLower x h ∉ ((SSet.boundary n).unionProd
      DaggerNativeWalkingRelativeGenerators.zeroSubcomplex.{u}).obj _ := by
  rw [notMem_relative_iff]
  change Function.Surjective
    (fun k ↦ ((deleteWords (coordinates x) (lastActive (coordinates x) h)).val k).1) ∧ _
  constructor
  · apply deleteWords_surjective (coordinates x) _ hs
    exact ⟨firstTrue (coordinates x) h,
      ne_of_lt (firstTrue_lt_lastActive (coordinates x) h ht),
      (lastActive_level (coordinates x) h).symm⟩
  · exact deleteWords_true (coordinates x) _ ht h

theorem initialLower_relative
    (hs : Function.Surjective (fun k ↦ ((coordinates x).val k).1))
    (ht : ((coordinates x).val (firstActive (coordinates x) h)).2 = false) :
    initialLower x h ∉ ((SSet.boundary n).unionProd
      DaggerNativeWalkingRelativeGenerators.zeroSubcomplex.{u}).obj _ := by
  rw [notMem_relative_iff]
  change Function.Surjective
    (fun k ↦ ((deleteWords (coordinates x) (firstActive (coordinates x) h)).val k).1) ∧ _
  constructor
  · apply deleteWords_surjective (coordinates x) _ hs
    exact ⟨firstTrue (coordinates x) h,
      (ne_of_gt (firstActive_lt_firstTrue (coordinates x) h ht)),
      (firstActive_level (coordinates x) h).symm⟩
  · exact deleteWords_true (coordinates x) _ ht h

theorem terminalLower_nonDegenerate
    (hs : Function.Surjective (fun k ↦ ((coordinates x).val k).1))
    (ha : active (coordinates x) h < Fin.last n)
    (ht : ((coordinates x).val (lastActive (coordinates x) h)).2 = false)
    (hx : x ∈ (Δ[n] ⊗ J.{u}).nonDegenerate (d + 2)) :
    terminalLower x h ∈ (Δ[n] ⊗ J.{u}).nonDegenerate (d + 1) := by
  have hi := terminal_deletion (coordinates x) h hs ha ht
  obtain ⟨p, hp⟩ := exists_innerSlot _ hi.1 hi.2
  have hh := delta_inner_nonDegenerate x hx p (terminal_gap (coordinates x) h ht p hp)
  simpa only [hp] using hh

theorem initialLower_nonDegenerate
    (hs : Function.Surjective (fun k ↦ ((coordinates x).val k).1))
    (ha : 0 < active (coordinates x) h)
    (ht : ((coordinates x).val (firstActive (coordinates x) h)).2 = false)
    (hx : x ∈ (Δ[n] ⊗ J.{u}).nonDegenerate (d + 2)) :
    initialLower x h ∈ (Δ[n] ⊗ J.{u}).nonDegenerate (d + 1) := by
  have hi := initial_deletion (coordinates x) h hs ha ht
  obtain ⟨p, hp⟩ := exists_innerSlot _ hi.1 hi.2
  have hh := delta_inner_nonDegenerate x hx p (initial_gap (coordinates x) h ht p hp)
  simpa only [hp] using hh

theorem terminalLower_boundary
    (hx : x ∈ (Δ[n] ⊗ J.{u}).nonDegenerate (d + 2))
    (ht : ((coordinates x).val (lastActive (coordinates x) h)).2 = false)
    (hn : ∃ k, ((coordinates (terminalLower x h)).val k).2 = true) :
    (lastActive (coordinates (terminalLower x h)) hn).succ = lastActive (coordinates x) h ∧
      ((coordinates (terminalLower x h)).val
        (lastActive (coordinates (terminalLower x h)) hn)).2 = true :=
  terminal_deleted_boundary (coordinates x) h ((nonDegenerate_iff x).mp hx) ht hn

theorem initialLower_boundary
    (hx : x ∈ (Δ[n] ⊗ J.{u}).nonDegenerate (d + 2))
    (ht : ((coordinates x).val (firstActive (coordinates x) h)).2 = false)
    (hn : ∃ k, ((coordinates (initialLower x h)).val k).2 = true) :
    (firstActive (coordinates (initialLower x h)) hn).castSucc = firstActive (coordinates x) h ∧
      ((coordinates (initialLower x h)).val
        (firstActive (coordinates (initialLower x h)) hn)).2 = true :=
  initial_deleted_boundary (coordinates x) h ((nonDegenerate_iff x).mp hx) ht hn

end
end DaggerNativeWalkingBlockUpperDeletions
