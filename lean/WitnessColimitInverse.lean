import SimplexInverseWitnessCategory
import OriginalQuasiReplacementsAccessible
import Mathlib.CategoryTheory.Limits.Comma

/-!
# The actual inverse maps in whole witness diagrams descend over original arrow colimits

The original left and right colimits are sent through the whole functor R.
Strict inverse preservation supplies a genuine cocone and its unique inverse map.
-/
set_option autoImplicit false
open CategoryTheory Limits
open DaggerSimplexInverseWitnessCategory
universe u v w
namespace DaggerWitnessColimitInverse
noncomputable section
variable {C : Type w} [Category.{v} C] {J : Type u} [SmallCategory J]
  [HasColimitsOfShape J C] (R : C ⥤ SSet.{u}) [PreservesColimitsOfShape J R]
  {F : J ⥤ Witness R} {c : Cocone (F ⋙ forget R)}

abbrev leftDiagram : J ⥤ SSet.{u} := F ⋙ forget R ⋙ Arrow.leftFunc ⋙ R

abbrev rightDiagram : J ⥤ SSet.{u} := F ⋙ forget R ⋙ Arrow.rightFunc ⋙ R

abbrev leftCocone : Cocone (leftDiagram R (F := F)) :=
  R.mapCocone (Arrow.leftFunc.mapCocone c)

abbrev rightCocone : Cocone (rightDiagram R (F := F)) :=
  R.mapCocone (Arrow.rightFunc.mapCocone c)

def leftIsColimit (hc : IsColimit c) : IsColimit (leftCocone R (c := c)) :=
  isColimitOfPreserves R (isColimitOfPreserves Arrow.leftFunc hc)

def rightIsColimit (hc : IsColimit c) : IsColimit (rightCocone R (c := c)) :=
  isColimitOfPreserves R (isColimitOfPreserves Arrow.rightFunc hc)

def inverseCocone : Cocone (rightDiagram R (F := F)) where
  pt := R.obj c.pt.left
  ι :=
    { app := fun j ↦ (F.obj j).data.inv ≫ R.map (c.ι.app j).left
      naturality := by
        intro i j f
        change R.map (F.map f).square.right ≫
          ((F.obj j).data.inv ≫ R.map (c.ι.app j).left) =
            (F.obj i).data.inv ≫ R.map (c.ι.app i).left
        have h := congrArg
          (fun t : (F.obj i).arrow ⟶ c.pt ↦ t.left) (c.w f)
        change (F.map f).square.left ≫ (c.ι.app j).left = (c.ι.app i).left at h
        rw [← Category.assoc, (F.map f).inverse_commutes, Category.assoc, ← R.map_comp, h] }

def inverse (hc : IsColimit c) : R.obj c.pt.right ⟶ R.obj c.pt.left :=
  (rightIsColimit R hc).desc (inverseCocone R (c := c))

theorem inverse_fac (hc : IsColimit c) (j : J) :
    R.map (c.ι.app j).right ≫ inverse R hc =
      (F.obj j).data.inv ≫ R.map (c.ι.app j).left :=
  (rightIsColimit R hc).fac (inverseCocone R (c := c)) j

theorem left_composite_square (hc : IsColimit c) (j : J) :
    (R.map (F.obj j).arrow.hom ≫ (F.obj j).data.inv) ≫ R.map (c.ι.app j).left =
      R.map (c.ι.app j).left ≫ (R.map c.pt.hom ≫ inverse R hc) := by
  have h := congrArg R.map (Arrow.w (c.ι.app j))
  rw [R.map_comp, R.map_comp] at h
  change R.map (c.ι.app j).left ≫ R.map c.pt.hom =
    R.map (F.obj j).arrow.hom ≫ R.map (c.ι.app j).right at h
  rw [Category.assoc, ← inverse_fac R hc j, ← Category.assoc, ← h, Category.assoc]

theorem right_composite_square (hc : IsColimit c) (j : J) :
    ((F.obj j).data.inv ≫ R.map (F.obj j).arrow.hom) ≫ R.map (c.ι.app j).right =
      R.map (c.ι.app j).right ≫ (inverse R hc ≫ R.map c.pt.hom) := by
  have h := congrArg R.map (Arrow.w (c.ι.app j))
  rw [R.map_comp, R.map_comp] at h
  change R.map (c.ι.app j).left ≫ R.map c.pt.hom =
    R.map (F.obj j).arrow.hom ≫ R.map (c.ι.app j).right at h
  rw [Category.assoc, ← h, ← Category.assoc, ← inverse_fac R hc j, Category.assoc]

theorem inverse_target_square (hc : IsColimit c) (Y : Witness R) (a : c.pt ⟶ Y.arrow)
    (ha : ∀ j, R.map ((c.ι.app j ≫ a).right) ≫ Y.data.inv =
      (F.obj j).data.inv ≫ R.map ((c.ι.app j ≫ a).left)) :
    R.map a.right ≫ Y.data.inv = inverse R hc ≫ R.map a.left := by
  apply (rightIsColimit R hc).hom_ext
  intro j
  change R.map (c.ι.app j).right ≫ (R.map a.right ≫ Y.data.inv) =
    R.map (c.ι.app j).right ≫ (inverse R hc ≫ R.map a.left)
  simp only [← Category.assoc]
  rw [inverse_fac R hc j]
  simpa only [Arrow.comp_left, Arrow.comp_right, R.map_comp, ← Category.assoc] using ha j

end
end DaggerWitnessColimitInverse
