import RelativeInverseActualStage
import ArrowEndpointPresentability

/-! Actual relative data use the common rank of the original base arrow. -/
set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial
open DaggerNativeJoyalWeakSimplexInverse DaggerInverseTriangleCellFamily
universe u v w
namespace DaggerRelativeInverseBasePresentability
noncomputable section

theorem exists_stage {C : Type w} [Category.{v} C] [HasTerminal C]
    [HasColimitsOfSize.{u, u} C] (R : C ⥤ SSet.{u})
    (κ : Cardinal.{u}) [Fact κ.IsRegular] [R.IsCardinalAccessible κ]
    (hR : ∀ X : C, IsCardinalPresentable X κ → IsCardinalPresentable (R.obj X) κ)
    {J : Type u} [SmallCategory J] [IsCardinalFiltered J κ]
    {F : J ⥤ Arrow C} {c : Cocone F} (hc : IsColimit c)
    (d : SimplexInverseData (R.map c.pt.hom)) (i : J)
    [IsCardinalPresentable (F.obj i) κ] :
    ∃ (j : J) (t : i ⟶ j) (e : DaggerRectangularInverseWitnessData.Data R (F.map t)),
      e.inv ≫ R.map (c.ι.app j).left = R.map (c.ι.app i).right ≫ d.inv ∧
      (∀ r : Kind, DaggerRectangularInverseWitnessData.Square
        (R.map (c.ι.app i).left) (R.map (c.ι.app j).left)
          (DaggerRawIsoTriangleCells.cell e.left r)
          (DaggerRawIsoTriangleCells.cell d.left r)) ∧
      (∀ r : Kind, DaggerRectangularInverseWitnessData.Square
        (R.map (c.ι.app i).right) (R.map (c.ι.app j).right)
          (DaggerRawIsoTriangleCells.cell e.right r)
          (DaggerRawIsoTriangleCells.cell d.right r)) := by
  have : IsCardinalPresentable (F.obj i).left κ :=
    DaggerArrowEndpointPresentability.left_presentable C κ (F.obj i)
  have : IsCardinalPresentable (F.obj i).right κ :=
    DaggerArrowEndpointPresentability.right_presentable C κ (F.obj i)
  have : IsCardinalPresentable (R.obj (F.obj i).left) κ := hR _ inferInstance
  have : IsCardinalPresentable (R.obj (F.obj i).right) κ := hR _ inferInstance
  have : PreservesColimitsOfShape J R :=
    R.preservesColimitsOfShape_of_isCardinalAccessible κ J
  exact DaggerRelativeInverseActualStage.exists_stage R κ hc d i

end
end DaggerRelativeInverseBasePresentability
