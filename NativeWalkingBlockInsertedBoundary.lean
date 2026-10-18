import NativeWalkingBlockLowerExtensions
import NativeWalkingInsertedBlocks

/-! Both actual block insertions land at the new computed false block end. -/
set_option autoImplicit false
open CategoryTheory Simplicial MonoidalCategory
open DaggerActualFreeWalkingIsoIntegerObstruction DaggerNativeWalkingSimplexWords
open DaggerNativeWalkingWordBlocks DaggerNativeWalkingWordInsertions
open DaggerNativeWalkingMarkedWordOperators DaggerNativeWalkingInsertedBlocks
open DaggerNativeWalkingBlockLowerExtensions
universe u
namespace DaggerNativeWalkingBlockInsertedBoundary
noncomputable section
theorem active_congr {n d : ℕ} {w v : Words n d} (he : w = v)
    (h : ∃ k, (w.val k).2 = true) (hn : ∃ k, (v.val k).2 = true) :
    active w h = active v hn := by
  cases he
  rfl

theorem lastActive_congr {n d : ℕ} {w v : Words n d} (he : w = v)
    (h : ∃ k, (w.val k).2 = true) (hn : ∃ k, (v.val k).2 = true) :
    lastActive w h = lastActive v hn := by
  cases he
  rfl

theorem firstActive_congr {n d : ℕ} {w v : Words n d} (he : w = v)
    (h : ∃ k, (w.val k).2 = true) (hn : ∃ k, (v.val k).2 = true) :
    firstActive w h = firstActive v hn := by
  cases he
  rfl

variable {n d : ℕ} (x : (Δ[n] ⊗ J.{u} : SSet.{u}) _⦋d + 1⦌)
  (h : ∃ k, ((coordinates x).val k).2 = true)
  (hs : Function.Surjective (fun k ↦ ((coordinates x).val k).1))

theorem terminalUpper_boundary (ha : active (coordinates x) h < Fin.last n)
    (hn : ∃ k, ((coordinates (terminalUpper x h hs ha)).val k).2 = true) :
    active (coordinates (terminalUpper x h hs ha)) hn = active (coordinates x) h ∧
      lastActive (coordinates (terminalUpper x h hs ha)) hn =
        (lastActive (coordinates x) h).succ ∧
      ((coordinates (terminalUpper x h hs ha)).val
        (lastActive (coordinates (terminalUpper x h hs ha)) hn)).2 = false := by
  let y := terminalUpper x h hs ha
  let i := (lastActive (coordinates x) h).succ
  let a := active (coordinates x) h
  have hread : (coordinates y).val = Fin.insert (coordinates x).val i (a, false) :=
    terminalUpper_read x h hs ha
  have hm : Monotone (fun k ↦ (Fin.insert (coordinates x).val i (a, false) k).1) := by
    rw [← hread]
    exact (coordinates y).property
  have hw : coordinates y = insertWords (coordinates x) i (a, false) hm := Subtype.ext hread
  have hn' : ∃ k, ((insertWords (coordinates x) i (a, false) hm).val k).2 = true := by
    rwa [← hw]
  have hactive := active_insert_false (coordinates x) h i a hm hn'
  have hlast := lastActive_insert_terminal (coordinates x) h hm hn'
  have hay := (active_congr hw hn hn').trans hactive
  have hly := (lastActive_congr hw hn hn').trans hlast
  refine ⟨hay, hly, ?_⟩
  change ((coordinates y).val (lastActive (coordinates y) hn)).2 = false
  rw [hly, hread, Fin.insert_self]

theorem initialUpper_boundary (ha : 0 < active (coordinates x) h)
    (hn : ∃ k, ((coordinates (initialUpper x h hs ha)).val k).2 = true) :
    active (coordinates (initialUpper x h hs ha)) hn = active (coordinates x) h ∧
      firstActive (coordinates (initialUpper x h hs ha)) hn =
        (firstActive (coordinates x) h).castSucc ∧
      ((coordinates (initialUpper x h hs ha)).val
        (firstActive (coordinates (initialUpper x h hs ha)) hn)).2 = false := by
  let y := initialUpper x h hs ha
  let i := (firstActive (coordinates x) h).castSucc
  let a := active (coordinates x) h
  have hread : (coordinates y).val = Fin.insert (coordinates x).val i (a, false) :=
    initialUpper_read x h hs ha
  have hm : Monotone (fun k ↦ (Fin.insert (coordinates x).val i (a, false) k).1) := by
    rw [← hread]
    exact (coordinates y).property
  have hw : coordinates y = insertWords (coordinates x) i (a, false) hm := Subtype.ext hread
  have hn' : ∃ k, ((insertWords (coordinates x) i (a, false) hm).val k).2 = true := by
    rwa [← hw]
  have hactive := active_insert_false (coordinates x) h i a hm hn'
  have hfirst := firstActive_insert_initial (coordinates x) h hm hn'
  have hay := (active_congr hw hn hn').trans hactive
  have hfy := (firstActive_congr hw hn hn').trans hfirst
  refine ⟨hay, hfy, ?_⟩
  change ((coordinates y).val (firstActive (coordinates y) hn)).2 = false
  rw [hfy, hread, Fin.insert_self]

end
end DaggerNativeWalkingBlockInsertedBoundary
