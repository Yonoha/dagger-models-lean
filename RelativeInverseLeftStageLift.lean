import RelativeArrowStageFacs
import RectangularTrianglePrePost

/-! The actual left inverse triangles lift after the whole inverse has factored. -/
set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial
open DaggerNativeJoyalWeakSimplexInverse DaggerNativeHoIsoTriangles DaggerNativeIhomHoObjects
open DaggerRawIsoTriangleCells DaggerInverseTriangleCellFamily
open DaggerOriginalArrowWitnessStageDiagrams DaggerRelativeArrowStageFacs
universe u v w
namespace DaggerRelativeInverseLeftStageLift
noncomputable section
variable {C : Type w} [Category.{v} C] {J : Type u} [SmallCategory J]
  [HasColimitsOfShape J C] (R : C ⥤ SSet.{u}) [PreservesColimitsOfShape J R]
  {F : J ⥤ Arrow C} {c : Cocone F}

theorem lift (κ : Cardinal.{u}) [Fact κ.IsRegular] [IsCardinalFiltered J κ]
    (hc : IsColimit c) (d : SimplexInverseData (R.map c.pt.hom)) (i : J)
    [IsCardinalPresentable (R.obj (F.obj i).left) κ]
    {j : J} (t : i ⟶ j) (g : R.obj (F.obj i).right ⟶ R.obj (F.obj j).left)
    (hg : g ≫ R.map (c.ι.app j).left = R.map (c.ι.app i).right ≫ d.inv) :
    ∃ (k : J) (u : j ⟶ k)
      (e : IsoTriangles ((ihom (R.obj (F.obj i).left)).obj (R.obj (F.obj k).left))
        (homObject (R.map (F.obj i).hom ≫ (g ≫ R.map (F.map u).left)))
        (homObject (R.map (F.map (t ≫ u)).left))),
      ∀ r : Kind, DaggerRectangularInverseWitnessData.Square
        (R.map (c.ι.app i).left) (R.map (c.ι.app k).left)
          (DaggerRawIsoTriangleCells.cell e r)
          (DaggerRawIsoTriangleCells.cell d.left r) := by
  let H := R.map (c.ι.app i).left ≫ (R.map c.pt.hom ≫ d.inv)
  let K := R.map (c.ι.app i).left ≫ 𝟙 _
  let dd := DaggerRectangularTrianglePrePost.pre (R.map (c.ι.app i).left)
    (R.map c.pt.hom ≫ d.inv) (𝟙 _) d.left
  have hh : (R.map (F.obj i).hom ≫ g) ≫ R.map (c.ι.app j).left = H := by
    have hw : R.map (c.ι.app i).left ≫ R.map c.pt.hom =
        R.map (F.obj i).hom ≫ R.map (c.ι.app i).right := map_square R (c.ι.app i)
    dsimp [H]
    rw [Category.assoc, hg, ← Category.assoc, ← hw, Category.assoc]
  have hk : R.map (F.map t).left ≫ R.map (c.ι.app j).left = K := by
    dsimp [K]
    rw [left_leg_comp, Category.comp_id]
  obtain ⟨k, u, e, he⟩ := DaggerRectangularHomTriangleStageLift.lift κ
    (leftIsColimit R hc) (R.obj (F.obj i).left) H K dd j
    (R.map (F.obj i).hom ≫ g) (R.map (F.map t).left) hh hk
  have hunit : R.map (F.map t).left ≫ R.map (F.map u).left =
      R.map (F.map (t ≫ u)).left := by
    rw [F.map_comp, Arrow.comp_left, R.map_comp]
  let e' := DaggerNativeIsoTriangleCellTransport.cast
    (congrArg homObject (Category.assoc (R.map (F.obj i).hom) g (R.map (F.map u).left)))
    (congrArg homObject hunit) e
  refine ⟨k, u, e', fun r ↦ ?_⟩
  change ((ihom (R.obj (F.obj i).left)).map (R.map (c.ι.app k).left)).app
    (op ⦋r.degree⦌)
          (DaggerRawIsoTriangleCells.cell e' r) =
      ((MonoidalClosed.pre (R.map (c.ι.app i).left)).app (R.obj c.pt.left)).app
        (op ⦋r.degree⦌)
          (DaggerRawIsoTriangleCells.cell d.left r)
  dsimp [e']
  rw [DaggerRawIsoTriangleCasts.cell_cast]
  exact (he r).trans (DaggerRectangularTrianglePrePost.cell_pre _ _ _ d.left r)

end
end DaggerRelativeInverseLeftStageLift
