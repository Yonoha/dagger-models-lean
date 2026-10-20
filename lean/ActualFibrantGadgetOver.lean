import ActualFibrantGadgetExtensions
import Mathlib.CategoryTheory.Comma.Over.Basic

/-! The actual gadget extension is functorial over the fixed original coherent nerve. -/

set_option autoImplicit false
open CategoryTheory DaggerModels OrdinaryRigidification OriginalOrdinaryLocalKanReplacement
open DaggerActualFibrantGadgetData DaggerActualFibrantGadgetExtensions
universe u

namespace DaggerActualFibrantGadgetOver
noncomputable section

/-- Extend every full simplicial map and over-triangle to the same fixed target. -/
def over (D : SimplicialCat.{u, u}) (r : replacement.obj D ⟶ D) :
    Over (coherentNerve.obj D) ⥤ Over (coherentNerve.obj D) where
  obj X := Over.mk (extension D r X.hom)
  map {X Y} f := Over.homMk (gadget.map f.left) (by
    have h := extension_naturality D r f.left Y.hom
    rw [Over.w f] at h
    exact h)
  map_id X := by
    apply CostructuredArrow.hom_ext
    exact gadget.map_id X.left
  map_comp f g := by
    apply CostructuredArrow.hom_ext
    exact gadget.map_comp f.left g.left

/-- A retraction of the replacement unit gives the original gadget unit over the target. -/
def overUnit (D : SimplicialCat.{u, u}) (r : replacement.obj D ⟶ D)
    (hr : OriginalOrdinaryLocalKanReplacement.unit.app D ≫ r = 𝟙 D) :
    𝟭 (Over (coherentNerve.obj D)) ⟶ over D r where
  app X := Over.homMk (DaggerActualFibrantGadgetData.unit.app X.left)
    (unit_extension D r hr X.hom)
  naturality {X Y} f := by
    apply CostructuredArrow.hom_ext
    exact DaggerActualFibrantGadgetData.unit.naturality f.left

/-- The object keeps the entire extended map, not only its vertices. -/
theorem over_obj_hom (D : SimplicialCat.{u, u}) (r : replacement.obj D ⟶ D)
    (X : Over (coherentNerve.obj D)) : ((over D r).obj X).hom = extension D r X.hom := rfl

/-- Every original over-arrow is carried by the chosen gadget functor on its full left map. -/
theorem over_map_left (D : SimplicialCat.{u, u}) (r : replacement.obj D ⟶ D)
    {X Y : Over (coherentNerve.obj D)} (f : X ⟶ Y) :
    ((over D r).map f).left = gadget.map f.left := rfl

/-- The natural comparison retains the actual unit on every underlying simplicial set. -/
theorem overUnit_app_left (D : SimplicialCat.{u, u}) (r : replacement.obj D ⟶ D)
    (hr : OriginalOrdinaryLocalKanReplacement.unit.app D ≫ r = 𝟙 D)
    (X : Over (coherentNerve.obj D)) :
    ((overUnit D r hr).app X).left = DaggerActualFibrantGadgetData.unit.app X.left := rfl

end
end DaggerActualFibrantGadgetOver
