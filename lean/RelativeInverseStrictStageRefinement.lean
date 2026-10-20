import RelativeInverseRawCellRefinement
import RectangularCellPostSquares

/-! One later stage enforces the crossed inverse and all eight chosen cell equations. -/
set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial MonoidalCategory
open DaggerNativeJoyalWeakSimplexInverse DaggerInverseTriangleCellFamily
open DaggerNativeEndomorphismSimplexMaps DaggerRectangularInverseWitnessData
open DaggerOriginalArrowWitnessStageDiagrams DaggerRelativeArrowStageFacs
universe u v w
namespace DaggerRelativeInverseStrictStageRefinement

variable {C : Type w} [Category.{v} C] {J : Type u} [SmallCategory J]
  [HasColimitsOfShape J C] (R : C ⥤ SSet.{u}) [PreservesColimitsOfShape J R]
  {F : J ⥤ Arrow C} {c : Cocone F}

theorem exists_stage (κ : Cardinal.{u}) [Fact κ.IsRegular] [IsCardinalFiltered J κ]
    (hc : IsColimit c) (d : SimplexInverseData (R.map c.pt.hom))
    {i j k : J} (p : i ⟶ j) (q : j ⟶ k) (e : Data R (F.map p)) (f : Data R (F.map q))
    [IsCardinalPresentable (R.obj (F.obj i).left) κ]
    [IsCardinalPresentable (R.obj (F.obj i).right) κ]
    (he : e.inv ≫ R.map (c.ι.app j).left = R.map (c.ι.app i).right ≫ d.inv)
    (hf : f.inv ≫ R.map (c.ι.app k).left = R.map (c.ι.app j).right ≫ d.inv)
    (heL : ∀ r : Kind, Square (R.map (c.ι.app i).left) (R.map (c.ι.app j).left)
      (DaggerRawIsoTriangleCells.cell e.left r) (DaggerRawIsoTriangleCells.cell d.left r))
    (heR : ∀ r : Kind, Square (R.map (c.ι.app i).right) (R.map (c.ι.app j).right)
      (DaggerRawIsoTriangleCells.cell e.right r) (DaggerRawIsoTriangleCells.cell d.right r))
    (hfL : ∀ r : Kind, Square (R.map (c.ι.app j).left) (R.map (c.ι.app k).left)
      (DaggerRawIsoTriangleCells.cell f.left r) (DaggerRawIsoTriangleCells.cell d.left r))
    (hfR : ∀ r : Kind, Square (R.map (c.ι.app j).right) (R.map (c.ι.app k).right)
      (DaggerRawIsoTriangleCells.cell f.right r) (DaggerRawIsoTriangleCells.cell d.right r)) :
    ∃ (l : J) (v : k ⟶ l),
      R.map (F.map p).right ≫ (f.inv ≫ R.map (F.map v).left) =
        e.inv ≫ R.map (F.map (q ≫ v)).left ∧
      (∀ r : Kind, Square (R.map (F.map p).left) (R.map (F.map (q ≫ v)).left)
        (DaggerRawIsoTriangleCells.cell e.left r)
        (((ihom (R.obj (F.obj j).left)).map (R.map (F.map v).left)).app (op ⦋r.degree⦌)
          (DaggerRawIsoTriangleCells.cell f.left r))) ∧
      (∀ r : Kind, Square (R.map (F.map p).right) (R.map (F.map (q ≫ v)).right)
        (DaggerRawIsoTriangleCells.cell e.right r)
        (((ihom (R.obj (F.obj j).right)).map (R.map (F.map v).right)).app (op ⦋r.degree⦌)
          (DaggerRawIsoTriangleCells.cell f.right r))) := by
  obtain ⟨l, v, hL, hR⟩ := DaggerRelativeInverseRawCellRefinement.exists_stage R κ hc d
    p q e f heL heR hfL hfR
  have hf' : (f.inv ≫ R.map (F.map v).left) ≫ R.map (c.ι.app l).left =
      R.map (c.ι.app j).right ≫ d.inv := inverse_fac_post R c v f.inv d.inv hf
  obtain ⟨m, w, hw⟩ := DaggerRelativeInverseMapStageRefinement.exists_stage R κ hc
    p (q ≫ v) e.inv (f.inv ≫ R.map (F.map v).left) d.inv he hf'
  refine ⟨m, v ≫ w, ?_, ?_, ?_⟩
  · simpa only [Functor.map_comp, Arrow.comp_left, Category.assoc] using hw
  · intro r
    have h := DaggerRectangularCellPostSquares.post_target
      (R.map (F.map p).left) (R.map (F.map (q ≫ v)).left) (R.map (F.map w).left)
      _ _ (hL r)
    simpa only [Functor.map_comp, Arrow.comp_left, Category.assoc,
      FunctorToTypes.comp, types_comp_apply] using h
  · intro r
    have h := DaggerRectangularCellPostSquares.post_target
      (R.map (F.map p).right) (R.map (F.map (q ≫ v)).right) (R.map (F.map w).right)
      _ _ (hR r)
    simpa only [Functor.map_comp, Arrow.comp_right, Category.assoc,
      FunctorToTypes.comp, types_comp_apply] using h

end DaggerRelativeInverseStrictStageRefinement
