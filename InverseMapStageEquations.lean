import FiniteStageEquations
import Mathlib.AlgebraicTopology.SimplicialSet.Basic

/-! The whole inverse-map commutation equation becomes strict at a later stage. -/
set_option autoImplicit false
open CategoryTheory Limits
universe u
namespace DaggerInverseMapStageEquations

theorem equation_after_colimit {X Y L R L' R' : SSet.{u}}
    (v : Y ⟶ X) (a : X ⟶ L) (b : Y ⟶ R) (d : R ⟶ L)
    (l : L ⟶ L') (r : R ⟶ R') (g : R' ⟶ L')
    (hleg : r ≫ g = d ≫ l) (hglobal : (b ≫ r) ≫ g = v ≫ (a ≫ l)) :
    (v ≫ a) ≫ l = (b ≫ d) ≫ l := by
  simpa only [Category.assoc, hleg] using hglobal.symm

theorem inverse_commutes_eventually {J : Type u} [SmallCategory J]
    (κ : Cardinal.{u}) [Fact κ.IsRegular] [IsCardinalFiltered J κ]
    (L R : J ⥤ SSet.{u}) (cL : Cocone L) (hcL : IsColimit cL) (cR : Cocone R)
    (d : ∀ j, R.obj j ⟶ L.obj j) (g : cR.pt ⟶ cL.pt)
    (hleg : ∀ j, cR.ι.app j ≫ g = d j ≫ cL.ι.app j)
    (hstage : ∀ {i j} (t : i ⟶ j), R.map t ≫ d j = d i ≫ L.map t)
    {X Y : SSet.{u}} [IsCardinalPresentable Y κ] (v : Y ⟶ X)
    {i : J} (a : X ⟶ L.obj i) (b : Y ⟶ R.obj i)
    (hglobal : (b ≫ cR.ι.app i) ≫ g = v ≫ (a ≫ cL.ι.app i)) :
    ∃ (j : J) (t : i ⟶ j),
      (b ≫ R.map t) ≫ d j = v ≫ (a ≫ L.map t) := by
  have he := equation_after_colimit v a b (d i) (cL.ι.app i) (cR.ι.app i) g
    (hleg i) hglobal
  obtain ⟨j, t, ht⟩ := IsCardinalPresentable.exists_eq_of_isColimit' κ hcL
    (v ≫ a) (b ≫ d i) he
  refine ⟨j, t, ?_⟩
  simpa only [Category.assoc, hstage t] using ht.symm

end DaggerInverseMapStageEquations
