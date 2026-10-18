import WholeWitnessSides
import InverseMapStageEquations

/-! The whole inverse commutes after one actual original arrow transition. -/
set_option autoImplicit false
open CategoryTheory Limits
open DaggerSimplexInverseWitnessCategory DaggerWholeWitnessSides
universe u v w
namespace DaggerWholeWitnessInverseStageLifts

variable {C : Type w} [Category.{v} C] {J : Type u} [SmallCategory J]
  [HasColimitsOfShape J C] (R : C ⥤ SSet.{u}) [PreservesColimitsOfShape J R]

theorem inverse_commutes_eventually (κ : Cardinal.{u}) [Fact κ.IsRegular]
    [IsCardinalFiltered J κ] {F : J ⥤ Witness R} {c : Cocone F} (hc : IsColimit c)
    (X : Witness R) [IsCardinalPresentable (R.obj X.arrow.right) κ]
    (h : X ⟶ c.pt) {i : J} (a : X.arrow ⟶ (F.obj i).arrow)
    (hfac : a ≫ (c.ι.app i).square = h.square) :
    ∃ (j : J) (t : i ⟶ j),
      R.map (a ≫ (F.map t).square).right ≫ (F.obj j).data.inv =
        X.data.inv ≫ R.map (a ≫ (F.map t).square).left := by
  have hl := congrArg (fun f : X.arrow ⟶ c.pt.arrow ↦ f.left) hfac
  have hr := congrArg (fun f : X.arrow ⟶ c.pt.arrow ↦ f.right) hfac
  change a.left ≫ (c.ι.app i).square.left = h.square.left at hl
  change a.right ≫ (c.ι.app i).square.right = h.square.right at hr
  have hh : (R.map a.right ≫ R.map (c.ι.app i).square.right) ≫ c.pt.data.inv =
      X.data.inv ≫ (R.map a.left ≫ R.map (c.ι.app i).square.left) := by
    rw [← R.map_comp, ← R.map_comp, hl, hr]
    exact h.inverse_commutes
  obtain ⟨j, t, ht⟩ := DaggerInverseMapStageEquations.inverse_commutes_eventually κ
    (X := R.obj X.arrow.left) (Y := R.obj X.arrow.right)
    (F ⋙ sideFunctor R false) (F ⋙ sideFunctor R true)
    ((sideFunctor R false).mapCocone c) (sideIsColimit R hc false)
    ((sideFunctor R true).mapCocone c) (fun j ↦ (F.obj j).data.inv) c.pt.data.inv
    (fun j ↦ (c.ι.app j).inverse_commutes)
    (fun {_ _} t ↦ (F.map t).inverse_commutes) X.data.inv (R.map a.left) (R.map a.right) hh
  exact ⟨j, t, by simpa only [Arrow.comp_right, Arrow.comp_left, R.map_comp] using ht⟩

end DaggerWholeWitnessInverseStageLifts
