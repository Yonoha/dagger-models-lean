import CountableCrossedInverseColimit
import ColimitFixedTargetCells

/-! All chosen rectangular raw cells descend over the actual original Arrow colimit. -/
set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial MonoidalCategory
open DaggerRelativeInverseLadderData DaggerCountableArrowStageDiagrams
open DaggerInverseTriangleCellFamily DaggerRectangularInverseWitnessData
open DaggerNativeEndomorphismSimplexMaps
universe u v w
namespace DaggerCountableCrossedCellColimit
noncomputable section
local instance nativeBraiding : BraidedCategory SSet.{u} :=
  BraidedCategory.ofCartesianMonoidalCategory
local instance tensorRightPreserves (K : SSet.{u}) :
    PreservesColimitsOfShape ℕ (tensorRight K) :=
  preservesColimitsOfShape_of_natIso (BraidedCategory.tensorLeftIsoTensorRight K)

variable {C : Type w} [Category.{v} C] [HasColimitsOfShape ℕ C]
  (R : C ⥤ SSet.{u}) [PreservesColimitsOfShape ℕ R]
  {D : ℕ ⥤ Arrow C} (c : Cocone D) (e : Ladder R D) (r : Kind)

def leftCellCocone : Cocone (leftDiagram R (D := D) ⋙ tensorRight Δ[r.degree]) where
  pt := R.obj c.pt.left
  ι := NatTrans.ofSequence
    (fun n ↦ simplexHomEquiv (R.obj (D.obj n).left) (R.obj (D.obj (n + 1)).left)
      r.degree (DaggerRawIsoTriangleCells.cell (e.data n).left r) ≫
        R.map (c.ι.app (n + 1)).left) (by
    intro n
    change (R.map (step D n).left ▷ Δ[r.degree]) ≫
      (simplexHomEquiv (R.obj (D.obj (n + 1)).left) (R.obj (D.obj (n + 1 + 1)).left)
        r.degree (DaggerRawIsoTriangleCells.cell (e.data (n + 1)).left r) ≫
          R.map (c.ι.app (n + 1 + 1)).left) = _ ≫ 𝟙 _
    rw [Category.comp_id, ← Category.assoc]
    rw [← (square_iff_tensor_map _ _ _ _ _).1 (e.left_compatible n r),
      Category.assoc, left_leg])

def rightCellCocone : Cocone (rightDiagram R (D := D) ⋙ tensorRight Δ[r.degree]) where
  pt := R.obj c.pt.right
  ι := NatTrans.ofSequence
    (fun n ↦ simplexHomEquiv (R.obj (D.obj n).right) (R.obj (D.obj (n + 1)).right)
      r.degree (DaggerRawIsoTriangleCells.cell (e.data n).right r) ≫
        R.map (c.ι.app (n + 1)).right) (by
    intro n
    change (R.map (step D n).right ▷ Δ[r.degree]) ≫
      (simplexHomEquiv (R.obj (D.obj (n + 1)).right) (R.obj (D.obj (n + 1 + 1)).right)
        r.degree (DaggerRawIsoTriangleCells.cell (e.data (n + 1)).right r) ≫
          R.map (c.ι.app (n + 1 + 1)).right) = _ ≫ 𝟙 _
    rw [Category.comp_id, ← Category.assoc]
    rw [← (square_iff_tensor_map _ _ _ _ _).1 (e.right_compatible n r),
      Category.assoc, right_leg])

def leftCell (hc : IsColimit c) :
    ((ihom (R.obj c.pt.left)).obj (R.obj c.pt.left)).obj (op ⦋r.degree⦌) :=
  (simplexHomEquiv (R.obj c.pt.left) (R.obj c.pt.left) r.degree).symm
    ((isColimitOfPreserves (tensorRight Δ[r.degree]) (leftIsColimit R c hc)).desc
      (leftCellCocone R c e r))

def rightCell (hc : IsColimit c) :
    ((ihom (R.obj c.pt.right)).obj (R.obj c.pt.right)).obj (op ⦋r.degree⦌) :=
  (simplexHomEquiv (R.obj c.pt.right) (R.obj c.pt.right) r.degree).symm
    ((isColimitOfPreserves (tensorRight Δ[r.degree]) (rightIsColimit R c hc)).desc
      (rightCellCocone R c e r))

theorem leftCell_square (hc : IsColimit c) (n : ℕ) :
    Square (R.map (c.ι.app n).left) (R.map (c.ι.app (n + 1)).left)
      (DaggerRawIsoTriangleCells.cell (e.data n).left r) (leftCell R c e r hc) := by
  apply (square_iff_tensor_map _ _ _ _ _).2
  change simplexHomEquiv (R.obj (D.obj n).left) (R.obj (D.obj (n + 1)).left)
      r.degree (DaggerRawIsoTriangleCells.cell (e.data n).left r) ≫
        R.map (c.ι.app (n + 1)).left =
    R.map (c.ι.app n).left ▷ Δ[r.degree] ≫
      simplexHomEquiv (R.obj c.pt.left) (R.obj c.pt.left) r.degree (leftCell R c e r hc)
  rw [leftCell, Equiv.apply_symm_apply]
  exact ((isColimitOfPreserves (tensorRight Δ[r.degree]) (leftIsColimit R c hc)).fac
    (leftCellCocone R c e r) n).symm

theorem rightCell_square (hc : IsColimit c) (n : ℕ) :
    Square (R.map (c.ι.app n).right) (R.map (c.ι.app (n + 1)).right)
      (DaggerRawIsoTriangleCells.cell (e.data n).right r) (rightCell R c e r hc) := by
  apply (square_iff_tensor_map _ _ _ _ _).2
  change simplexHomEquiv (R.obj (D.obj n).right) (R.obj (D.obj (n + 1)).right)
      r.degree (DaggerRawIsoTriangleCells.cell (e.data n).right r) ≫
        R.map (c.ι.app (n + 1)).right =
    R.map (c.ι.app n).right ▷ Δ[r.degree] ≫
      simplexHomEquiv (R.obj c.pt.right) (R.obj c.pt.right) r.degree (rightCell R c e r hc)
  rw [rightCell, Equiv.apply_symm_apply]
  exact ((isColimitOfPreserves (tensorRight Δ[r.degree]) (rightIsColimit R c hc)).fac
    (rightCellCocone R c e r) n).symm

end
end DaggerCountableCrossedCellColimit
