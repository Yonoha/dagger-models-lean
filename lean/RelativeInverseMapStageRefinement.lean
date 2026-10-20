import RectangularCellStageRefinements

/-! A crossed inverse becomes strictly compatible with the preceding crossed inverse. -/
set_option autoImplicit false
open CategoryTheory Limits
open DaggerOriginalArrowWitnessStageDiagrams DaggerRelativeArrowStageFacs
universe u v w
namespace DaggerRelativeInverseMapStageRefinement

variable {C : Type w} [Category.{v} C] {J : Type u} [SmallCategory J]
  [HasColimitsOfShape J C] (R : C ⥤ SSet.{u}) [PreservesColimitsOfShape J R]
  {F : J ⥤ Arrow C} {c : Cocone F}

theorem exists_stage (κ : Cardinal.{u}) [Fact κ.IsRegular] [IsCardinalFiltered J κ]
    (hc : IsColimit c) {i j k : J} (p : i ⟶ j) (q : j ⟶ k)
    [IsCardinalPresentable (R.obj (F.obj i).right) κ]
    (g : R.obj (F.obj i).right ⟶ R.obj (F.obj j).left)
    (h : R.obj (F.obj j).right ⟶ R.obj (F.obj k).left)
    (G : R.obj c.pt.right ⟶ R.obj c.pt.left)
    (hg : g ≫ R.map (c.ι.app j).left = R.map (c.ι.app i).right ≫ G)
    (hh : h ≫ R.map (c.ι.app k).left = R.map (c.ι.app j).right ≫ G) :
    ∃ (l : J) (v : k ⟶ l), R.map (F.map p).right ≫ (h ≫ R.map (F.map v).left) =
      g ≫ R.map (F.map (q ≫ v)).left := by
  have heq : (R.map (F.map p).right ≫ h) ≫ R.map (c.ι.app k).left =
      (g ≫ R.map (F.map q).left) ≫ R.map (c.ι.app k).left := by
    rw [Category.assoc, hh, ← Category.assoc, right_leg_comp,
      Category.assoc g, left_leg_comp, hg]
  obtain ⟨l, v, hv⟩ := IsCardinalPresentable.exists_eq_of_isColimit' κ
    (leftIsColimit R hc) (R.map (F.map p).right ≫ h)
    (g ≫ R.map (F.map q).left) heq
  refine ⟨l, v, ?_⟩
  simpa only [Functor.map_comp, Arrow.comp_left, Category.assoc] using hv

end DaggerRelativeInverseMapStageRefinement
