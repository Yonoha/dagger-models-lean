import RelativeInverseLadderState
import Mathlib.CategoryTheory.Functor.OfSequence

/-! A countable ladder of actual original Arrow stages with every chosen cell coherent. -/
set_option autoImplicit false
open CategoryTheory Limits
open DaggerNativeJoyalWeakSimplexInverse DaggerRelativeInverseTrackedData
open DaggerRelativeInverseLadderState
universe u v w
namespace DaggerRelativeInverseCountableLadder
noncomputable section
variable {C : Type w} [Category.{v} C] {J : Type u} [SmallCategory J]
  [HasColimitsOfShape J C] (R : C ⥤ SSet.{u}) [PreservesColimitsOfShape J R]
  {F : J ⥤ Arrow C} (c : Cocone F) (d : SimplexInverseData (R.map c.pt.hom))
  (κ : Cardinal.{u}) [Fact κ.IsRegular] [IsCardinalFiltered J κ]
  (hc : IsColimit c)
  (hX : ∀ j : J, IsCardinalPresentable (R.obj (F.obj j).left) κ ∧
    IsCardinalPresentable (R.obj (F.obj j).right) κ) (i : J)

def states : ℕ → State R c d :=
  Nat.rec (initial R c d κ hc hX i) (fun _ e ↦ next R c d κ hc hX e)

def stages (n : ℕ) : J := (states R c d κ hc hX i n).start

def transition (n : ℕ) : stages R c d κ hc hX i n ⟶ stages R c d κ hc hX i (n + 1) :=
  (states R c d κ hc hX i n).transition

def witness (n : ℕ) : Tracked R c d (transition R c d κ hc hX i n) :=
  (states R c d κ hc hX i n).witness

theorem compatible (n : ℕ) :
    Compatible R c d (witness R c d κ hc hX i n) (witness R c d κ hc hX i (n + 1)) :=
  next_compatible R c d κ hc hX (states R c d κ hc hX i n)

def index : ℕ ⥤ J := Functor.ofSequence (transition R c d κ hc hX i)

theorem index_zero : (index R c d κ hc hX i).obj 0 = i := rfl

theorem index_succ (n : ℕ) :
    (index R c d κ hc hX i).map (homOfLE (n.le_add_right 1)) =
      transition R c d κ hc hX i n :=
  Functor.ofSequence_map_homOfLE_succ _ n

def arrowDiagram : ℕ ⥤ Arrow C := index R c d κ hc hX i ⋙ F

def coconeToOriginal : Cocone (arrowDiagram R c d κ hc hX i) :=
  c.whisker (index R c d κ hc hX i)

end
end DaggerRelativeInverseCountableLadder
