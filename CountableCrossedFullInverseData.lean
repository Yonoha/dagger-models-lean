import ColimitRectangularIsoTriangles
import CountableCrossedCellTargetSquares

/-! The countable crossed ladder gives the full ORIGINAL inverse and cancellation triangles. -/
set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial
open DaggerNativeJoyalWeakSimplexInverse DaggerNativeHoIsoTriangles DaggerNativeIhomHoObjects
open DaggerInverseTriangleCellFamily DaggerRelativeInverseLadderData
open DaggerCountableArrowStageDiagrams DaggerCountableCrossedInverseColimit
open DaggerCountableCrossedCellColimit DaggerColimitRectangularIsoTriangles
universe u v w
namespace DaggerCountableCrossedFullInverseData
noncomputable section
variable {C : Type w} [Category.{v} C] [HasColimitsOfShape ℕ C]
  (R : C ⥤ SSet.{u}) [PreservesColimitsOfShape ℕ R]
  {D : ℕ ⥤ Arrow C} (c : Cocone D) (e : Ladder R D)

def leftTriangles (hc : IsColimit c) :
    IsoTriangles ((ihom (R.obj c.pt.left)).obj (R.obj c.pt.left))
      (homObject (R.map c.pt.hom ≫ inverse R c e hc)) (homObject (𝟙 (R.obj c.pt.left))) :=
  colimitTriangles (F := leftDiagram R (D := D)) (c := leftCocone R c)
    (fun n ↦ R.map (D.obj n).hom ≫ (e.data n).inv)
    (fun n ↦ R.map (step D n).left) (fun n ↦ (e.data n).left)
    (fun r ↦ leftCell R c e r hc) (fun n r ↦ leftCell_square R c e r hc n)
    (leftIsColimit R c hc) (R.map c.pt.hom ≫ inverse R c e hc) (𝟙 _)
    (left_composite R c e hc) (fun n ↦ by simpa using left_leg R c n)

def rightTriangles (hc : IsColimit c) :
    IsoTriangles ((ihom (R.obj c.pt.right)).obj (R.obj c.pt.right))
      (homObject (inverse R c e hc ≫ R.map c.pt.hom)) (homObject (𝟙 (R.obj c.pt.right))) :=
  colimitTriangles (F := rightDiagram R (D := D)) (c := rightCocone R c)
    (fun n ↦ (e.data n).inv ≫ R.map (D.obj (n + 1)).hom)
    (fun n ↦ R.map (step D n).right) (fun n ↦ (e.data n).right)
    (fun r ↦ rightCell R c e r hc) (fun n r ↦ rightCell_square R c e r hc n)
    (rightIsColimit R c hc) (inverse R c e hc ≫ R.map c.pt.hom) (𝟙 _)
    (right_composite R c e hc) (fun n ↦ by simpa using right_leg R c n)

def data (hc : IsColimit c) : SimplexInverseData (R.map c.pt.hom) :=
  ⟨inverse R c e hc, leftTriangles R c e hc, rightTriangles R c e hc⟩

theorem inv_data (hc : IsColimit c) : (data R c e hc).inv = inverse R c e hc := rfl

theorem cell_left (hc : IsColimit c) (r : Kind) :
    DaggerRawIsoTriangleCells.cell (data R c e hc).left r = leftCell R c e r hc := by
  change DaggerRawIsoTriangleCells.cell (leftTriangles R c e hc) r = _
  rw [leftTriangles, cell_colimitTriangles]

theorem cell_right (hc : IsColimit c) (r : Kind) :
    DaggerRawIsoTriangleCells.cell (data R c e hc).right r = rightCell R c e r hc := by
  change DaggerRawIsoTriangleCells.cell (rightTriangles R c e hc) r = _
  rw [rightTriangles, cell_colimitTriangles]

end
end DaggerCountableCrossedFullInverseData
