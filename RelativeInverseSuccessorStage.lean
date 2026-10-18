import RelativeInverseTrackedPost

/-! Every tracked relative inverse has an actual compatible successor tracked stage. -/
set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial
open DaggerNativeJoyalWeakSimplexInverse DaggerInverseTriangleCellFamily
open DaggerRectangularInverseWitnessData DaggerRelativeInverseTrackedData
universe u v w
namespace DaggerRelativeInverseSuccessorStage

variable {C : Type w} [Category.{v} C] {J : Type u} [SmallCategory J]
  [HasColimitsOfShape J C] (R : C ⥤ SSet.{u}) [PreservesColimitsOfShape J R]
  {F : J ⥤ Arrow C} (c : Cocone F) (d : SimplexInverseData (R.map c.pt.hom))

theorem exists_next (κ : Cardinal.{u}) [Fact κ.IsRegular] [IsCardinalFiltered J κ]
    (hc : IsColimit c) {i j : J} (p : i ⟶ j) (e : Tracked R c d p)
    [IsCardinalPresentable (R.obj (F.obj i).left) κ]
    [IsCardinalPresentable (R.obj (F.obj i).right) κ]
    [IsCardinalPresentable (R.obj (F.obj j).left) κ]
    [IsCardinalPresentable (R.obj (F.obj j).right) κ] :
    ∃ (k : J) (q : j ⟶ k) (f : Tracked R c d q), Compatible R c d e f := by
  obtain ⟨k, q, ⟨f⟩⟩ := exists_tracked R c d κ hc j
  obtain ⟨l, v, hv, hL, hR⟩ := DaggerRelativeInverseStrictStageRefinement.exists_stage
    R κ hc d p q e.data f.data e.inverse_fac f.inverse_fac
    e.left_fac e.right_fac f.left_fac f.right_fac
  refine ⟨l, q ≫ v, DaggerRelativeInverseTrackedPost.post R c d q v f, ?_⟩
  change R.map (F.map p).right ≫ (DaggerRelativeInverseTrackedPost.stageData R c d q v f).inv =
      e.data.inv ≫ R.map (F.map (q ≫ v)).left ∧ _
  rw [DaggerRelativeInverseTrackedPost.stage_inv]
  refine ⟨hv, ?_, ?_⟩
  · intro r
    change Square (R.map (F.map p).left) (R.map (F.map (q ≫ v)).left)
      (DaggerRawIsoTriangleCells.cell e.data.left r)
      (DaggerRawIsoTriangleCells.cell
        (DaggerRelativeInverseTrackedPost.stageData R c d q v f).left r)
    rw [DaggerRelativeInverseTrackedPost.stage_cell_left]
    exact hL r
  · intro r
    change Square (R.map (F.map p).right) (R.map (F.map (q ≫ v)).right)
      (DaggerRawIsoTriangleCells.cell e.data.right r)
      (DaggerRawIsoTriangleCells.cell
        (DaggerRelativeInverseTrackedPost.stageData R c d q v f).right r)
    rw [DaggerRelativeInverseTrackedPost.stage_cell_right]
    exact hR r

end DaggerRelativeInverseSuccessorStage
