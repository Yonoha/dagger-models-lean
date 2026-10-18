import RectangularInverseTransitionCast
import RelativeInverseStrictStageRefinement

/-! Relative data retain the ENTIRE prescribed original witness at every stage. -/
set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial
open DaggerNativeJoyalWeakSimplexInverse DaggerInverseTriangleCellFamily
open DaggerRectangularInverseWitnessData
universe u v w
namespace DaggerRelativeInverseTrackedData
variable {C : Type w} [Category.{v} C] {J : Type u} [SmallCategory J]
  (R : C ⥤ SSet.{u}) {F : J ⥤ Arrow C} (c : Cocone F)
  (d : SimplexInverseData (R.map c.pt.hom))

structure Tracked {i j : J} (p : i ⟶ j) where
  data : Data R (F.map p)
  inverse_fac : data.inv ≫ R.map (c.ι.app j).left = R.map (c.ι.app i).right ≫ d.inv
  left_fac : ∀ r : Kind, Square (R.map (c.ι.app i).left) (R.map (c.ι.app j).left)
    (DaggerRawIsoTriangleCells.cell data.left r) (DaggerRawIsoTriangleCells.cell d.left r)
  right_fac : ∀ r : Kind, Square (R.map (c.ι.app i).right) (R.map (c.ι.app j).right)
    (DaggerRawIsoTriangleCells.cell data.right r) (DaggerRawIsoTriangleCells.cell d.right r)

def Compatible {i j k : J} {p : i ⟶ j} {q : j ⟶ k}
    (e : Tracked R c d p) (f : Tracked R c d q) : Prop :=
  R.map (F.map p).right ≫ f.data.inv = e.data.inv ≫ R.map (F.map q).left ∧
  (∀ r : Kind, Square (R.map (F.map p).left) (R.map (F.map q).left)
    (DaggerRawIsoTriangleCells.cell e.data.left r)
    (DaggerRawIsoTriangleCells.cell f.data.left r)) ∧
  (∀ r : Kind, Square (R.map (F.map p).right) (R.map (F.map q).right)
    (DaggerRawIsoTriangleCells.cell e.data.right r)
    (DaggerRawIsoTriangleCells.cell f.data.right r))

theorem exists_tracked [HasColimitsOfShape J C] [PreservesColimitsOfShape J R]
    (κ : Cardinal.{u}) [Fact κ.IsRegular] [IsCardinalFiltered J κ] (hc : IsColimit c) (i : J)
    [IsCardinalPresentable (R.obj (F.obj i).left) κ]
    [IsCardinalPresentable (R.obj (F.obj i).right) κ] :
    ∃ (j : J) (p : i ⟶ j), Nonempty (Tracked R c d p) := by
  obtain ⟨j, p, e, h, hL, hR⟩ := DaggerRelativeInverseActualStage.exists_stage R κ hc d i
  exact ⟨j, p, ⟨⟨e, h, hL, hR⟩⟩⟩

end DaggerRelativeInverseTrackedData
