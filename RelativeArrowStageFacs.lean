import OriginalArrowWitnessStageDiagrams

/-! Exact squares and cocone equations for the original Arrow stages under R. -/
set_option autoImplicit false
open CategoryTheory Limits
universe u v w
namespace DaggerRelativeArrowStageFacs
variable {C : Type w} [Category.{v} C] (R : C ⥤ SSet.{u})

theorem map_square {a b : Arrow C} (p : a ⟶ b) :
    R.map p.left ≫ R.map b.hom = R.map a.hom ≫ R.map p.right := by
  have h := congrArg R.map (Arrow.w p)
  rw [R.map_comp, R.map_comp] at h
  exact h

variable {J : Type u} [SmallCategory J] {F : J ⥤ Arrow C} (c : Cocone F)

theorem left_leg_comp {i j : J} (t : i ⟶ j) :
    R.map (F.map t).left ≫ R.map (c.ι.app j).left = R.map (c.ι.app i).left := by
  have h := congrArg (fun f : F.obj i ⟶ c.pt ↦ f.left) (c.w t)
  change (F.map t).left ≫ (c.ι.app j).left = (c.ι.app i).left at h
  exact (R.map_comp _ _).symm.trans (congrArg R.map h)

theorem right_leg_comp {i j : J} (t : i ⟶ j) :
    R.map (F.map t).right ≫ R.map (c.ι.app j).right = R.map (c.ι.app i).right := by
  have h := congrArg (fun f : F.obj i ⟶ c.pt ↦ f.right) (c.w t)
  change (F.map t).right ≫ (c.ι.app j).right = (c.ι.app i).right at h
  exact (R.map_comp _ _).symm.trans (congrArg R.map h)

theorem inverse_fac_post {i j k : J} (u : j ⟶ k)
    (g : R.obj (F.obj i).right ⟶ R.obj (F.obj j).left)
    (h : R.obj c.pt.right ⟶ R.obj c.pt.left)
    (hg : g ≫ R.map (c.ι.app j).left = R.map (c.ι.app i).right ≫ h) :
    (g ≫ R.map (F.map u).left) ≫ R.map (c.ι.app k).left =
      R.map (c.ι.app i).right ≫ h := by
  rw [Category.assoc, left_leg_comp, hg]

end DaggerRelativeArrowStageFacs
