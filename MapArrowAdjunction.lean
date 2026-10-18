import Mathlib.CategoryTheory.Comma.Arrow
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Comma
import Mathlib.CategoryTheory.Presentable.Basic

set_option autoImplicit false

open CategoryTheory Limits

universe v₁ v₂ u₁ u₂ v u w

namespace DaggerMapArrow

noncomputable section

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
variable {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)

/-- The original adjunction applied at both endpoints of the original Arrow functors. -/
def mapArrowAdjunction : F.mapArrow ⊣ G.mapArrow where
  unit := (Functor.mapArrowFunctor C C).map adj.unit
  counit := (Functor.mapArrowFunctor D D).map adj.counit
  left_triangle_components f :=
    Arrow.hom_ext _ _ (adj.left_triangle_components f.left)
      (adj.left_triangle_components f.right)
  right_triangle_components f :=
    Arrow.hom_ext _ _ (adj.right_triangle_components f.left)
      (adj.right_triangle_components f.right)

theorem unit_left (f : Arrow C) :
    ((mapArrowAdjunction adj).unit.app f).left = adj.unit.app f.left := rfl

theorem unit_right (f : Arrow C) :
    ((mapArrowAdjunction adj).unit.app f).right = adj.unit.app f.right := rfl

theorem counit_left (f : Arrow D) :
    ((mapArrowAdjunction adj).counit.app f).left = adj.counit.app f.left := rfl

theorem counit_right (f : Arrow D) :
    ((mapArrowAdjunction adj).counit.app f).right = adj.counit.app f.right := rfl

include adj in
/-- Existing left-adjoint preservation applies to the exact mapped-arrow functor. -/
theorem preservesColimits : PreservesColimitsOfSize.{v, u} F.mapArrow :=
  (mapArrowAdjunction adj).leftAdjoint_preservesColimits

include adj in
/-- All-colimit preservation gives accessibility at every regular cardinal. -/
theorem accessible (κ : Cardinal.{w}) [Fact κ.IsRegular] :
    F.mapArrow.IsCardinalAccessible κ := by
  have : PreservesColimitsOfSize.{w, w} F.mapArrow := preservesColimits adj
  infer_instance

variable {J : Type u} [Category.{v} J] {K : J ⥤ Arrow C}
variable {c : Cocone K} (hc : IsColimit c)

/-- Preserve the supplied cocone, including its full universal property. -/
def mapIsColimit : IsColimit (F.mapArrow.mapCocone c) := by
  have : PreservesColimitsOfSize.{v, u} F.mapArrow := preservesColimits adj
  exact isColimitOfPreserves F.mapArrow hc

/-- The universal arrow to any supplied target cocone. -/
def mapDesc (s : Cocone (K ⋙ F.mapArrow)) : F.mapArrow.obj c.pt ⟶ s.pt :=
  (mapIsColimit adj hc).desc s

theorem mapDesc_fac (s : Cocone (K ⋙ F.mapArrow)) (j : J) :
    F.mapArrow.map (c.ι.app j) ≫ mapDesc adj hc s = s.ι.app j :=
  (mapIsColimit adj hc).fac s j

theorem mapDesc_fac_left (s : Cocone (K ⋙ F.mapArrow)) (j : J) :
    F.map (c.ι.app j).left ≫ (mapDesc adj hc s).left = (s.ι.app j).left :=
  Arrow.hom.congr_left (mapDesc_fac adj hc s j)

theorem mapDesc_fac_right (s : Cocone (K ⋙ F.mapArrow)) (j : J) :
    F.map (c.ι.app j).right ≫ (mapDesc adj hc s).right = (s.ι.app j).right :=
  Arrow.hom.congr_right (mapDesc_fac adj hc s j)

theorem mapDesc_uniq (s : Cocone (K ⋙ F.mapArrow))
    (m : F.mapArrow.obj c.pt ⟶ s.pt)
    (h : ∀ j, F.mapArrow.map (c.ι.app j) ≫ m = s.ι.app j) :
    m = mapDesc adj hc s := (mapIsColimit adj hc).uniq s m h

theorem leftCocone_eq :
    (Arrow.leftFunc : Arrow D ⥤ D).mapCocone (F.mapArrow.mapCocone c) =
      F.mapCocone ((Arrow.leftFunc : Arrow C ⥤ C).mapCocone c) := rfl

theorem rightCocone_eq :
    (Arrow.rightFunc : Arrow D ⥤ D).mapCocone (F.mapArrow.mapCocone c) =
      F.mapCocone ((Arrow.rightFunc : Arrow C ⥤ C).mapCocone c) := rfl

/-- The exact left component cocone has its full universal property. -/
def leftMapIsColimit [HasColimitsOfShape J D] :
    IsColimit ((Arrow.leftFunc : Arrow D ⥤ D).mapCocone (F.mapArrow.mapCocone c)) :=
  isColimitOfPreserves (Arrow.leftFunc : Arrow D ⥤ D) (mapIsColimit adj hc)

/-- The exact right component cocone has its full universal property. -/
def rightMapIsColimit [HasColimitsOfShape J D] :
    IsColimit ((Arrow.rightFunc : Arrow D ⥤ D).mapCocone (F.mapArrow.mapCocone c)) :=
  isColimitOfPreserves (Arrow.rightFunc : Arrow D ⥤ D) (mapIsColimit adj hc)

end

end DaggerMapArrow
