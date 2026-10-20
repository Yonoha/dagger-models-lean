import NativeWalkingBlockSlots
import NativeWalkingNondegenerateInsertions

/-! Both block branches produce actual relative nondegenerate upper simplices. -/
set_option autoImplicit false
open CategoryTheory Simplicial MonoidalCategory
open DaggerActualFreeWalkingIsoIntegerObstruction DaggerNativeWalkingSimplexWords
open DaggerNativeWalkingWordBlocks DaggerNativeWalkingBlockSlots
open DaggerNativeWalkingNondegenerateInsertions
universe u
namespace DaggerNativeWalkingBlockLowerExtensions
noncomputable section
variable {n d : ℕ} (x : (Δ[n] ⊗ J.{u} : SSet.{u}) _⦋d + 1⦌)
  (h : ∃ i, ((coordinates x).val i).2 = true)
  (hs : Function.Surjective (fun i ↦ ((coordinates x).val i).1))

def terminalUpper (ha : active (coordinates x) h < Fin.last n) :
    (Δ[n] ⊗ J.{u} : SSet.{u}) _⦋d + 2⦌ :=
  inserted x (terminalSlot (coordinates x) h hs ha) (active (coordinates x) h, false)
    (terminal_left_le (coordinates x) h hs ha) (terminal_right_le (coordinates x) h hs ha)

def initialUpper (ha : 0 < active (coordinates x) h) :
    (Δ[n] ⊗ J.{u} : SSet.{u}) _⦋d + 2⦌ :=
  inserted x (initialSlot (coordinates x) h hs ha) (active (coordinates x) h, false)
    (initial_left_le (coordinates x) h hs ha) (initial_right_le (coordinates x) h hs ha)

theorem terminalUpper_face (ha : active (coordinates x) h < Fin.last n) :
    (Δ[n] ⊗ J.{u}).δ (lastActive (coordinates x) h).succ (terminalUpper x h hs ha) = x := by
  have hi : (terminalSlot (coordinates x) h hs ha).succ.castSucc =
      (lastActive (coordinates x) h).succ := by
    rw [← Fin.succ_castSucc, terminalSlot_castSucc]
  simpa only [hi] using delta_inserted x (terminalSlot (coordinates x) h hs ha)
    (active (coordinates x) h, false)
    (terminal_left_le (coordinates x) h hs ha) (terminal_right_le (coordinates x) h hs ha)

theorem initialUpper_face (ha : 0 < active (coordinates x) h) :
    (Δ[n] ⊗ J.{u}).δ (firstActive (coordinates x) h).castSucc (initialUpper x h hs ha) = x := by
  have hi : (initialSlot (coordinates x) h hs ha).succ.castSucc =
      (firstActive (coordinates x) h).castSucc := by rw [initialSlot_succ]
  simpa only [hi] using delta_inserted x (initialSlot (coordinates x) h hs ha)
    (active (coordinates x) h, false)
    (initial_left_le (coordinates x) h hs ha) (initial_right_le (coordinates x) h hs ha)

theorem terminalUpper_nonDegenerate (ha : active (coordinates x) h < Fin.last n)
    (ht : ((coordinates x).val (lastActive (coordinates x) h)).2 = true)
    (hx : x ∈ (Δ[n] ⊗ J.{u}).nonDegenerate (d + 1)) :
    terminalUpper x h hs ha ∈ (Δ[n] ⊗ J.{u}).nonDegenerate (d + 2) :=
  inserted_nonDegenerate x _ _ _ _ hx
    (terminal_neighbors_ne (coordinates x) h hs ha ht).1
    (terminal_neighbors_ne (coordinates x) h hs ha ht).2

theorem initialUpper_nonDegenerate (ha : 0 < active (coordinates x) h)
    (ht : ((coordinates x).val (firstActive (coordinates x) h)).2 = true)
    (hx : x ∈ (Δ[n] ⊗ J.{u}).nonDegenerate (d + 1)) :
    initialUpper x h hs ha ∈ (Δ[n] ⊗ J.{u}).nonDegenerate (d + 2) :=
  inserted_nonDegenerate x _ _ _ _ hx
    (initial_neighbors_ne (coordinates x) h hs ha ht).1
    (initial_neighbors_ne (coordinates x) h hs ha ht).2

theorem terminalUpper_relative (ha : active (coordinates x) h < Fin.last n)
    (hx : x ∉ ((SSet.boundary n).unionProd
      DaggerNativeWalkingRelativeGenerators.zeroSubcomplex.{u}).obj _) :
    terminalUpper x h hs ha ∉ ((SSet.boundary n).unionProd
      DaggerNativeWalkingRelativeGenerators.zeroSubcomplex.{u}).obj _ :=
  inserted_relative x _ _ _ _ hx

theorem initialUpper_relative (ha : 0 < active (coordinates x) h)
    (hx : x ∉ ((SSet.boundary n).unionProd
      DaggerNativeWalkingRelativeGenerators.zeroSubcomplex.{u}).obj _) :
    initialUpper x h hs ha ∉ ((SSet.boundary n).unionProd
      DaggerNativeWalkingRelativeGenerators.zeroSubcomplex.{u}).obj _ :=
  inserted_relative x _ _ _ _ hx

theorem terminalUpper_read (ha : active (coordinates x) h < Fin.last n) :
    (coordinates (terminalUpper x h hs ha)).val =
      Fin.insert (coordinates x).val (lastActive (coordinates x) h).succ
        (active (coordinates x) h, false) := by
  change Fin.insert (coordinates x).val (terminalSlot (coordinates x) h hs ha).succ.castSucc
    (active (coordinates x) h, false) = _
  rw [← Fin.succ_castSucc, terminalSlot_castSucc]

theorem initialUpper_read (ha : 0 < active (coordinates x) h) :
    (coordinates (initialUpper x h hs ha)).val =
      Fin.insert (coordinates x).val (firstActive (coordinates x) h).castSucc
        (active (coordinates x) h, false) := by
  change Fin.insert (coordinates x).val (initialSlot (coordinates x) h hs ha).succ.castSucc
    (active (coordinates x) h, false) = _
  rw [initialSlot_succ]

end
end DaggerNativeWalkingBlockLowerExtensions
