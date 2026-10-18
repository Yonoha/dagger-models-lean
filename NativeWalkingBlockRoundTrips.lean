import NativeWalkingBlockInsertedBoundary
import NativeWalkingBlockUpperDeletions
import WalkingWordOperationRoundTrips

/-! Both original block branches have exact two-sided simplex round trips. -/
set_option autoImplicit false
open CategoryTheory Simplicial MonoidalCategory
open DaggerActualFreeWalkingIsoIntegerObstruction DaggerNativeWalkingSimplexWords
open DaggerNativeWalkingWordBlocks DaggerNativeWalkingMarkedWordOperators
open DaggerNativeWalkingBlockLowerExtensions DaggerNativeWalkingBlockUpperDeletions
open DaggerNativeWalkingBlockInsertedBoundary DaggerWalkingWordOperationRoundTrips
universe u
namespace DaggerNativeWalkingBlockRoundTrips
noncomputable section

theorem terminalLower_terminalUpper {n d : ℕ}
    (x : (Δ[n] ⊗ J.{u} : SSet.{u}) _⦋d + 1⦌)
    (h : ∃ k, ((coordinates x).val k).2 = true)
    (hs : Function.Surjective (fun k ↦ ((coordinates x).val k).1))
    (ha : active (coordinates x) h < Fin.last n)
    (hn : ∃ k, ((coordinates (terminalUpper x h hs ha)).val k).2 = true) :
    terminalLower (terminalUpper x h hs ha) hn = x := by
  change (Δ[n] ⊗ J.{u}).δ (lastActive (coordinates (terminalUpper x h hs ha)) hn)
    (terminalUpper x h hs ha) = x
  rw [(terminalUpper_boundary x h hs ha hn).2.1]
  exact terminalUpper_face x h hs ha

theorem initialLower_initialUpper {n d : ℕ}
    (x : (Δ[n] ⊗ J.{u} : SSet.{u}) _⦋d + 1⦌)
    (h : ∃ k, ((coordinates x).val k).2 = true)
    (hs : Function.Surjective (fun k ↦ ((coordinates x).val k).1))
    (ha : 0 < active (coordinates x) h)
    (hn : ∃ k, ((coordinates (initialUpper x h hs ha)).val k).2 = true) :
    initialLower (initialUpper x h hs ha) hn = x := by
  change (Δ[n] ⊗ J.{u}).δ (firstActive (coordinates (initialUpper x h hs ha)) hn)
    (initialUpper x h hs ha) = x
  rw [(initialUpper_boundary x h hs ha hn).2.1]
  exact initialUpper_face x h hs ha

theorem terminalUpper_terminalLower {n d : ℕ}
    (x : (Δ[n] ⊗ J.{u} : SSet.{u}) _⦋d + 2⦌)
    (h : ∃ k, ((coordinates x).val k).2 = true)
    (hx : x ∈ (Δ[n] ⊗ J.{u}).nonDegenerate (d + 2))
    (ht : ((coordinates x).val (lastActive (coordinates x) h)).2 = false)
    (hn : ∃ k, ((coordinates (terminalLower x h)).val k).2 = true)
    (hsn : Function.Surjective (fun k ↦ ((coordinates (terminalLower x h)).val k).1))
    (han : active (coordinates (terminalLower x h)) hn < Fin.last n) :
    terminalUpper (terminalLower x h) hn hsn han = x := by
  apply (wordEquiv.{u} n (d + 2)).injective
  apply Subtype.ext
  change (coordinates (terminalUpper (terminalLower x h) hn hsn han)).val = (coordinates x).val
  rw [terminalUpper_read, (terminalLower_boundary x h hx ht hn).1]
  have ha : active (coordinates (terminalLower x h)) hn = active (coordinates x) h :=
    active_delete_false (coordinates x) h _ ht hn
  rw [ha]
  have hv : (active (coordinates x) h, false) =
      (coordinates x).val (lastActive (coordinates x) h) := by
    apply Prod.ext
    · exact (lastActive_level (coordinates x) h).symm
    · exact ht.symm
  rw [hv]
  exact insert_delete_val (coordinates x).val _

theorem initialUpper_initialLower {n d : ℕ}
    (x : (Δ[n] ⊗ J.{u} : SSet.{u}) _⦋d + 2⦌)
    (h : ∃ k, ((coordinates x).val k).2 = true)
    (hx : x ∈ (Δ[n] ⊗ J.{u}).nonDegenerate (d + 2))
    (ht : ((coordinates x).val (firstActive (coordinates x) h)).2 = false)
    (hn : ∃ k, ((coordinates (initialLower x h)).val k).2 = true)
    (hsn : Function.Surjective (fun k ↦ ((coordinates (initialLower x h)).val k).1))
    (han : 0 < active (coordinates (initialLower x h)) hn) :
    initialUpper (initialLower x h) hn hsn han = x := by
  apply (wordEquiv.{u} n (d + 2)).injective
  apply Subtype.ext
  change (coordinates (initialUpper (initialLower x h) hn hsn han)).val = (coordinates x).val
  rw [initialUpper_read, (initialLower_boundary x h hx ht hn).1]
  have ha : active (coordinates (initialLower x h)) hn = active (coordinates x) h :=
    active_delete_false (coordinates x) h _ ht hn
  rw [ha]
  have hv : (active (coordinates x) h, false) =
      (coordinates x).val (firstActive (coordinates x) h) := by
    apply Prod.ext
    · exact (firstActive_level (coordinates x) h).symm
    · exact ht.symm
  rw [hv]
  exact insert_delete_val (coordinates x).val _

end
end DaggerNativeWalkingBlockRoundTrips
