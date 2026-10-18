import CountableCrossedFullInverseData

/-! The descended witness maps to the original witness with all chosen data preserved. -/
set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial
open DaggerNativeJoyalWeakSimplexInverse DaggerRelativeInverseLadderData
open DaggerSimplexInverseWitnessCategory DaggerInverseTriangleCellFamily
open DaggerRectangularInverseWitnessData
universe u v w
namespace DaggerCountableCrossedWholeWitnessTarget
noncomputable section
variable {C : Type w} [Category.{v} C] [HasColimitsOfShape ℕ C]
  (R : C ⥤ SSet.{u}) [PreservesColimitsOfShape ℕ R]
  {D : ℕ ⥤ Arrow C} (c : Cocone D) (e : Ladder R D)

def witness (hc : IsColimit c) : Witness R :=
  ⟨c.pt, DaggerCountableCrossedFullInverseData.data R c e hc⟩

theorem left_square (hc : IsColimit c) (c₀ : Cocone D)
    (d : SimplexInverseData (R.map c₀.pt.hom)) (he : Over R D e c₀ d) :
    TriangleSquare (R.map (hc.desc c₀).left) (witness R c e hc).data.left d.left := by
  have h : ∀ r : Kind, Square (R.map (hc.desc c₀).left) (R.map (hc.desc c₀).left)
      (DaggerRawIsoTriangleCells.cell (witness R c e hc).data.left r)
      (DaggerRawIsoTriangleCells.cell d.left r) := by
    intro r
    change Square _ _
      (DaggerRawIsoTriangleCells.cell
        (DaggerCountableCrossedFullInverseData.data R c e hc).left r) _
    rw [DaggerCountableCrossedFullInverseData.cell_left]
    exact DaggerCountableCrossedCellTargetSquares.left_target R c e hc c₀ d he r
  exact ⟨h .forward, h .backward, h .leftTriangle, h .rightTriangle⟩

theorem right_square (hc : IsColimit c) (c₀ : Cocone D)
    (d : SimplexInverseData (R.map c₀.pt.hom)) (he : Over R D e c₀ d) :
    TriangleSquare (R.map (hc.desc c₀).right) (witness R c e hc).data.right d.right := by
  have h : ∀ r : Kind, Square (R.map (hc.desc c₀).right) (R.map (hc.desc c₀).right)
      (DaggerRawIsoTriangleCells.cell (witness R c e hc).data.right r)
      (DaggerRawIsoTriangleCells.cell d.right r) := by
    intro r
    change Square _ _
      (DaggerRawIsoTriangleCells.cell
        (DaggerCountableCrossedFullInverseData.data R c e hc).right r) _
    rw [DaggerCountableCrossedFullInverseData.cell_right]
    exact DaggerCountableCrossedCellTargetSquares.right_target R c e hc c₀ d he r
  exact ⟨h .forward, h .backward, h .leftTriangle, h .rightTriangle⟩

def target (hc : IsColimit c) (c₀ : Cocone D)
    (d : SimplexInverseData (R.map c₀.pt.hom)) (he : Over R D e c₀ d) :
    witness R c e hc ⟶ (⟨c₀.pt, d⟩ : Witness R) where
  square := hc.desc c₀
  inverse_commutes := DaggerCountableCrossedInverseTargetSquare.inverse_target R c e hc c₀ d he
  triangleLeft := left_square R c e hc c₀ d he
  triangleRight := right_square R c e hc c₀ d he

end
end DaggerCountableCrossedWholeWitnessTarget
