import RelativeInverseLeftStageLift

/-! Actual right inverse triangles lift over the same factored whole inverse. -/
set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial
open DaggerNativeJoyalWeakSimplexInverse DaggerNativeHoIsoTriangles DaggerNativeIhomHoObjects
open DaggerRawIsoTriangleCells DaggerInverseTriangleCellFamily
open DaggerOriginalArrowWitnessStageDiagrams DaggerRelativeArrowStageFacs
universe u v w
namespace DaggerRelativeInverseRightStageLift
noncomputable section
variable {C : Type w} [Category.{v} C] {J : Type u} [SmallCategory J]
  [HasColimitsOfShape J C] (R : C ⥤ SSet.{u}) [PreservesColimitsOfShape J R]
  {F : J ⥤ Arrow C} {c : Cocone F}

theorem lift (κ : Cardinal.{u}) [Fact κ.IsRegular] [IsCardinalFiltered J κ]
    (hc : IsColimit c) (d : SimplexInverseData (R.map c.pt.hom)) (i : J)
    [IsCardinalPresentable (R.obj (F.obj i).right) κ]
    {j : J} (t : i ⟶ j) (g : R.obj (F.obj i).right ⟶ R.obj (F.obj j).left)
    (hg : g ≫ R.map (c.ι.app j).left = R.map (c.ι.app i).right ≫ d.inv) :
    ∃ (k : J) (u : j ⟶ k)
      (e : IsoTriangles ((ihom (R.obj (F.obj i).right)).obj (R.obj (F.obj k).right))
        (homObject ((g ≫ R.map (F.map u).left) ≫ R.map (F.obj k).hom))
        (homObject (R.map (F.map (t ≫ u)).right))),
      ∀ r : Kind, DaggerRectangularInverseWitnessData.Square
        (R.map (c.ι.app i).right) (R.map (c.ι.app k).right)
          (DaggerRawIsoTriangleCells.cell e r)
          (DaggerRawIsoTriangleCells.cell d.right r) := by
  let H := R.map (c.ι.app i).right ≫ (d.inv ≫ R.map c.pt.hom)
  let K := R.map (c.ι.app i).right ≫ 𝟙 _
  let dd := DaggerRectangularTrianglePrePost.pre (R.map (c.ι.app i).right)
    (d.inv ≫ R.map c.pt.hom) (𝟙 _) d.right
  have hh : (g ≫ R.map (F.obj j).hom) ≫ R.map (c.ι.app j).right = H := by
    have hw : R.map (c.ι.app j).left ≫ R.map c.pt.hom =
        R.map (F.obj j).hom ≫ R.map (c.ι.app j).right := map_square R (c.ι.app j)
    dsimp [H]
    rw [Category.assoc, ← hw, ← Category.assoc, hg, Category.assoc]
  have hk : R.map (F.map t).right ≫ R.map (c.ι.app j).right = K := by
    dsimp [K]
    rw [right_leg_comp, Category.comp_id]
  obtain ⟨k, u, e, he⟩ := DaggerRectangularHomTriangleStageLift.lift κ
    (rightIsColimit R hc) (R.obj (F.obj i).right) H K dd j
    (g ≫ R.map (F.obj j).hom) (R.map (F.map t).right) hh hk
  have hv : (g ≫ R.map (F.obj j).hom) ≫ R.map (F.map u).right =
      (g ≫ R.map (F.map u).left) ≫ R.map (F.obj k).hom := by
    simpa only [Category.assoc] using congrArg (fun z ↦ g ≫ z) (map_square R (F.map u)).symm
  have hunit : R.map (F.map t).right ≫ R.map (F.map u).right =
      R.map (F.map (t ≫ u)).right := by
    rw [F.map_comp, Arrow.comp_right, R.map_comp]
  let e' := DaggerNativeIsoTriangleCellTransport.cast (congrArg homObject hv)
    (congrArg homObject hunit) e
  refine ⟨k, u, e', fun r ↦ ?_⟩
  change ((ihom (R.obj (F.obj i).right)).map (R.map (c.ι.app k).right)).app
    (op ⦋r.degree⦌)
          (DaggerRawIsoTriangleCells.cell e' r) =
      ((MonoidalClosed.pre (R.map (c.ι.app i).right)).app (R.obj c.pt.right)).app
        (op ⦋r.degree⦌)
          (DaggerRawIsoTriangleCells.cell d.right r)
  dsimp [e']
  rw [DaggerRawIsoTriangleCasts.cell_cast]
  exact (he r).trans (DaggerRectangularTrianglePrePost.cell_pre _ _ _ d.right r)

end
end DaggerRelativeInverseRightStageLift
