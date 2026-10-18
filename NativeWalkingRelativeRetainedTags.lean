import NativeWalkingRelativeCells
import NativeWalkingRetainedBlockEnds

/-! Every different lower face of an upper cell has strictly larger first marked level. -/
set_option autoImplicit false
open CategoryTheory Simplicial MonoidalCategory
open DaggerNativeWalkingSimplexWords DaggerNativeWalkingWordBlocks
open DaggerNativeWalkingMarkedWordOperators DaggerNativeWalkingBlockInsertedBoundary
open DaggerNativeWalkingRetainedBlockEnds DaggerNativeWalkingRelativeCells
universe u
namespace DaggerNativeWalkingRelativeRetainedTags
noncomputable section

def endIndex {n d : ℕ} (x : Cell.{u} n d) : Fin (d + 1) :=
  if level x < Fin.last (n + 1) then lastActive (coordinates x.val) (true_exists x)
  else firstActive (coordinates x.val) (true_exists x)

theorem face_words {n d : ℕ} (x : Cell.{u} n (d + 1)) (y : Cell.{u} n d)
    (i : Fin (d + 2)) (he : (ambient.{u} n).δ i x.val = y.val) :
    deleteWords (coordinates x.val) i = coordinates y.val := by
  change coordinates ((ambient.{u} n).δ i x.val) = coordinates y.val
  exact congrArg coordinates he

theorem face_level_le {n d : ℕ} (x : Cell.{u} n (d + 1)) (y : Cell.{u} n d)
    (i : Fin (d + 2)) (he : (ambient.{u} n).δ i x.val = y.val) : level x ≤ level y := by
  have hw := face_words x y i he
  have hn : ∃ k, ((deleteWords (coordinates x.val) i).val k).2 = true := by
    rw [hw]
    exact true_exists y
  have hh := active_le_delete (coordinates x.val) (true_exists x) i hn
  have hc := active_congr hw hn (true_exists y)
  exact hh.trans_eq hc

theorem face_endTag_eq_of_level_eq {n d : ℕ}
    (x : Cell.{u} n (d + 1)) (y : Cell.{u} n d) (i : Fin (d + 2))
    (he : (ambient.{u} n).δ i x.val = y.val) (hi : i ≠ endIndex x)
    (hl : level y = level x) : endTag y = endTag x := by
  let v := deleteWords (coordinates x.val) i
  have hw : v = coordinates y.val := face_words x y i he
  have hn : ∃ k, (v.val k).2 = true := by rw [hw]; exact true_exists y
  have hc := active_congr hw hn (true_exists y)
  have ha : active v hn = active (coordinates x.val) (true_exists x) := hc.trans hl
  have hv : v.val = (coordinates y.val).val := congrArg Subtype.val hw
  by_cases hx : level x < Fin.last (n + 1)
  · have hy : level y < Fin.last (n + 1) := hl.trans_lt hx
    have hi' : i ≠ lastActive (coordinates x.val) (true_exists x) := by
      simpa only [endIndex, if_pos hx] using hi
    have hr := retained_terminal (coordinates x.val) (true_exists x) i hi' hn ha
    have hp := lastActive_congr hw hn (true_exists y)
    calc
      endTag y = (v.val (lastActive v hn)).2 := by
        rw [hv, hp]
        simp only [endTag, if_pos hy]
      _ = ((coordinates x.val).val (lastActive (coordinates x.val) (true_exists x))).2 := hr.2
      _ = endTag x := by simp only [endTag, if_pos hx]
  · have hy : ¬level y < Fin.last (n + 1) := by rw [hl]; exact hx
    have hi' : i ≠ firstActive (coordinates x.val) (true_exists x) := by
      simpa only [endIndex, if_neg hx] using hi
    have hr := retained_initial (coordinates x.val) (true_exists x) i hi' hn ha
    have hp := firstActive_congr hw hn (true_exists y)
    calc
      endTag y = (v.val (firstActive v hn)).2 := by
        rw [hv, hp]
        simp only [endTag, if_neg hy]
      _ = ((coordinates x.val).val (firstActive (coordinates x.val) (true_exists x))).2 := hr.2
      _ = endTag x := by simp only [endTag, if_neg hx]

theorem face_level_strict {n d : ℕ} (x : Cell.{u} n (d + 1)) (y : Cell.{u} n d)
    (i : Fin (d + 2)) (he : (ambient.{u} n).δ i x.val = y.val) (hi : i ≠ endIndex x)
    (hx : endTag x = false) (hy : endTag y = true) : level x < level y := by
  apply lt_of_le_of_ne (face_level_le x y i he)
  intro hlevel
  have hh := face_endTag_eq_of_level_eq x y i he hi hlevel.symm
  rw [hy, hx] at hh
  exact Bool.false_ne_true hh.symm

end
end DaggerNativeWalkingRelativeRetainedTags
