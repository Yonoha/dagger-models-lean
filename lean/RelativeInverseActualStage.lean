import RelativeInverseRightStageLift

/-!
# Actual relative inverse data above every prescribed original Arrow stage

The crossed inverse and all eight chosen raw cells map exactly to the original
whole inverse witness. No weakness of either individual stage is concluded.
-/
set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial
open DaggerNativeJoyalWeakSimplexInverse DaggerNativeHoIsoTriangles DaggerNativeIhomHoObjects
open DaggerRawIsoTriangleCells DaggerInverseTriangleCellFamily
open DaggerOriginalArrowWitnessStageDiagrams DaggerRelativeArrowStageFacs
universe u v w
namespace DaggerRelativeInverseActualStage
noncomputable section
variable {C : Type w} [Category.{v} C] {J : Type u} [SmallCategory J]
  [HasColimitsOfShape J C] (R : C ⥤ SSet.{u}) [PreservesColimitsOfShape J R]
  {F : J ⥤ Arrow C} {c : Cocone F}

theorem exists_stage (κ : Cardinal.{u}) [Fact κ.IsRegular] [IsCardinalFiltered J κ]
    (hc : IsColimit c) (d : SimplexInverseData (R.map c.pt.hom)) (i : J)
    [IsCardinalPresentable (R.obj (F.obj i).left) κ]
    [IsCardinalPresentable (R.obj (F.obj i).right) κ] :
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
  obtain ⟨j, t, g, hg⟩ := inverse_stage R κ hc d i
  obtain ⟨k, u, L, hL⟩ := DaggerRelativeInverseLeftStageLift.lift R κ hc d i t g hg
  let t₁ := t ≫ u
  let g₁ := g ≫ R.map (F.map u).left
  have hg₁ : g₁ ≫ R.map (c.ι.app k).left = R.map (c.ι.app i).right ≫ d.inv :=
    inverse_fac_post R c u g d.inv hg
  obtain ⟨l, v, T, hT⟩ := DaggerRelativeInverseRightStageLift.lift R κ hc d i t₁ g₁ hg₁
  have hunit : R.map (F.map t₁).left ≫ R.map (F.map v).left =
      R.map (F.map (t₁ ≫ v)).left := by
    rw [F.map_comp t₁ v, Arrow.comp_left, R.map_comp]
  let L' := DaggerNativeIsoTriangleCellTransport.cast
    (congrArg homObject (Category.assoc (R.map (F.obj i).hom) g₁ (R.map (F.map v).left)))
    (congrArg homObject hunit)
    (DaggerRectangularTrianglePrePost.post (R.map (F.map v).left)
      (R.map (F.obj i).hom ≫ g₁) (R.map (F.map t₁).left) L)
  let e : DaggerRectangularInverseWitnessData.Data R (F.map (t₁ ≫ v)) :=
    ⟨g₁ ≫ R.map (F.map v).left, L', T⟩
  refine ⟨l, t₁ ≫ v, e, inverse_fac_post R c v g₁ d.inv hg₁, ?_, ?_⟩
  · intro r
    change ((ihom (R.obj (F.obj i).left)).map (R.map (c.ι.app l).left)).app
      (op ⦋r.degree⦌)
          (DaggerRawIsoTriangleCells.cell L' r) =
        ((MonoidalClosed.pre (R.map (c.ι.app i).left)).app (R.obj c.pt.left)).app
          (op ⦋r.degree⦌)
          (DaggerRawIsoTriangleCells.cell d.left r)
    dsimp [L']
    rw [DaggerRawIsoTriangleCasts.cell_cast, DaggerRectangularTrianglePrePost.cell_post]
    have hm : (ihom (R.obj (F.obj i).left)).map (R.map (F.map v).left) ≫
        (ihom (R.obj (F.obj i).left)).map (R.map (c.ι.app l).left) =
          (ihom (R.obj (F.obj i).left)).map (R.map (c.ι.app k).left) := by
      rw [← Functor.map_comp, left_leg_comp]
    exact (congrArg
      (fun f : (ihom (R.obj (F.obj i).left)).obj (R.obj (F.obj k).left) ⟶
        (ihom (R.obj (F.obj i).left)).obj (R.obj c.pt.left) ↦
          f.app (op ⦋r.degree⦌)
          (DaggerRawIsoTriangleCells.cell L r)) hm).trans (hL r)
  · exact hT

end
end DaggerRelativeInverseActualStage
