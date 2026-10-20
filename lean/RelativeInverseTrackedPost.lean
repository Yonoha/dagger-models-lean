import RelativeInverseTrackedData
import RectangularCellLegPost

/-! Actual relative stages extend while retaining all of the prescribed original witness. -/
set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial
open DaggerNativeJoyalWeakSimplexInverse DaggerInverseTriangleCellFamily
open DaggerRectangularInverseWitnessData DaggerRelativeInverseTrackedData
open DaggerRelativeArrowStageFacs
universe u v w
namespace DaggerRelativeInverseTrackedPost
noncomputable section
variable {C : Type w} [Category.{v} C] {J : Type u} [SmallCategory J]
  (R : C ⥤ SSet.{u}) {F : J ⥤ Arrow C} (c : Cocone F)
  (d : SimplexInverseData (R.map c.pt.hom))
  {i j k : J} (p : i ⟶ j) (q : j ⟶ k) (e : Tracked R c d p)

def stageData : Data R (F.map (p ≫ q)) :=
  DaggerRectangularInverseTransitionCast.cast R (F.map_comp p q).symm
    (DaggerRectangularInverseDataPost.post R (F.map p) (F.map q) e.data)

theorem stage_inv : (stageData R c d p q e).inv = e.data.inv ≫ R.map (F.map q).left := by
  rw [stageData, DaggerRectangularInverseTransitionCast.inv_cast]
  rfl

theorem stage_cell_left (r : Kind) :
    DaggerRawIsoTriangleCells.cell (stageData R c d p q e).left r =
      ((ihom (R.obj (F.obj i).left)).map (R.map (F.map q).left)).app (op ⦋r.degree⦌)
        (DaggerRawIsoTriangleCells.cell e.data.left r) := by
  rw [stageData, DaggerRectangularInverseTransitionCast.cell_left,
    DaggerRectangularInverseDataPost.cell_left]

theorem stage_cell_right (r : Kind) :
    DaggerRawIsoTriangleCells.cell (stageData R c d p q e).right r =
      ((ihom (R.obj (F.obj i).right)).map (R.map (F.map q).right)).app (op ⦋r.degree⦌)
        (DaggerRawIsoTriangleCells.cell e.data.right r) := by
  rw [stageData, DaggerRectangularInverseTransitionCast.cell_right,
    DaggerRectangularInverseDataPost.cell_right]

def post : Tracked R c d (p ≫ q) where
  data := stageData R c d p q e
  inverse_fac := by
    rw [stage_inv]
    exact inverse_fac_post R c q e.data.inv d.inv e.inverse_fac
  left_fac r := by
    rw [stage_cell_left]
    exact DaggerRectangularCellLegPost.post_leg (R.map (c.ι.app i).left)
      (R.map (c.ι.app j).left) (R.map (F.map q).left) (R.map (c.ι.app k).left)
      (left_leg_comp R c q) _ _ (e.left_fac r)
  right_fac r := by
    rw [stage_cell_right]
    exact DaggerRectangularCellLegPost.post_leg (R.map (c.ι.app i).right)
      (R.map (c.ι.app j).right) (R.map (F.map q).right) (R.map (c.ι.app k).right)
      (right_leg_comp R c q) _ _ (e.right_fac r)

end
end DaggerRelativeInverseTrackedPost
