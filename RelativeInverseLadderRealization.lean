import RelativeInverseCountableLadder
import RelativeInverseLadderData

/-! The chosen countable stages give a literal original Arrow diagram and full crossed data. -/
set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial
open DaggerNativeJoyalWeakSimplexInverse DaggerInverseTriangleCellFamily
open DaggerRelativeInverseTrackedData DaggerRelativeInverseCountableLadder
open DaggerRelativeInverseLadderData
universe u v w
namespace DaggerRelativeInverseLadderRealization
noncomputable section
variable {C : Type w} [Category.{v} C] {J : Type u} [SmallCategory J]
  [HasColimitsOfShape J C] (R : C ⥤ SSet.{u}) [PreservesColimitsOfShape J R]
  {F : J ⥤ Arrow C} (c : Cocone F) (d : SimplexInverseData (R.map c.pt.hom))
  (κ : Cardinal.{u}) [Fact κ.IsRegular] [IsCardinalFiltered J κ]
  (hc : IsColimit c)
  (hX : ∀ j : J, IsCardinalPresentable (R.obj (F.obj j).left) κ ∧
    IsCardinalPresentable (R.obj (F.obj j).right) κ) (i : J)

abbrev D : ℕ ⥤ Arrow C := arrowDiagram R c d κ hc hX i

def data (n : ℕ) : DaggerRectangularInverseWitnessData.Data R (step (D R c d κ hc hX i) n) :=
  DaggerRectangularInverseTransitionCast.cast R
    (congrArg F.map (index_succ R c d κ hc hX i n)).symm
    (witness R c d κ hc hX i n).data

theorem data_inv (n : ℕ) : (data R c d κ hc hX i n).inv =
    (witness R c d κ hc hX i n).data.inv := by
  rw [data, DaggerRectangularInverseTransitionCast.inv_cast]

theorem data_left (n : ℕ) (r : Kind) :
    DaggerRawIsoTriangleCells.cell (data R c d κ hc hX i n).left r =
      DaggerRawIsoTriangleCells.cell (witness R c d κ hc hX i n).data.left r := by
  rw [data, DaggerRectangularInverseTransitionCast.cell_left]

theorem data_right (n : ℕ) (r : Kind) :
    DaggerRawIsoTriangleCells.cell (data R c d κ hc hX i n).right r =
      DaggerRawIsoTriangleCells.cell (witness R c d κ hc hX i n).data.right r := by
  rw [data, DaggerRectangularInverseTransitionCast.cell_right]

theorem step_eq (n : ℕ) : step (D R c d κ hc hX i) n =
    F.map (transition R c d κ hc hX i n) :=
  congrArg F.map (index_succ R c d κ hc hX i n)

def ladder : Ladder R (D R c d κ hc hX i) where
  data := data R c d κ hc hX i
  inverse_compatible n := by
    rw [data_inv, data_inv, step_eq, step_eq]
    exact (compatible R c d κ hc hX i n).1
  left_compatible n r := by
    rw [data_left, data_left, step_eq, step_eq]
    exact (compatible R c d κ hc hX i n).2.1 r
  right_compatible n r := by
    rw [data_right, data_right, step_eq, step_eq]
    exact (compatible R c d κ hc hX i n).2.2 r

theorem over : Over R (D R c d κ hc hX i) (ladder R c d κ hc hX i)
    (coconeToOriginal R c d κ hc hX i) d := by
  constructor
  · intro n
    change (data R c d κ hc hX i n).inv ≫
      R.map (c.ι.app ((index R c d κ hc hX i).obj (n + 1))).left = _
    rw [data_inv]
    exact (witness R c d κ hc hX i n).inverse_fac
  · intro n r
    change DaggerRectangularInverseWitnessData.Square _ _
      (DaggerRawIsoTriangleCells.cell (data R c d κ hc hX i n).left r) _
    rw [data_left]
    exact (witness R c d κ hc hX i n).left_fac r
  · intro n r
    change DaggerRectangularInverseWitnessData.Square _ _
      (DaggerRawIsoTriangleCells.cell (data R c d κ hc hX i n).right r) _
    rw [data_right]
    exact (witness R c d κ hc hX i n).right_fac r

end
end DaggerRelativeInverseLadderRealization
