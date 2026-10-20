import CountableCrossedCellColimit

/-! The descended whole inverse preserves the ENTIRE original chosen global inverse. -/
set_option autoImplicit false
open CategoryTheory Limits
open DaggerNativeJoyalWeakSimplexInverse DaggerRelativeInverseLadderData
open DaggerCountableArrowStageDiagrams DaggerCountableCrossedInverseColimit
universe u v w
namespace DaggerCountableCrossedInverseTargetSquare
variable {C : Type w} [Category.{v} C] [HasColimitsOfShape ℕ C]
  (R : C ⥤ SSet.{u}) [PreservesColimitsOfShape ℕ R]
  {D : ℕ ⥤ Arrow C} (c : Cocone D) (e : Ladder R D)

theorem inverse_target (hc : IsColimit c) (c₀ : Cocone D)
    (d : SimplexInverseData (R.map c₀.pt.hom)) (he : Over R D e c₀ d) :
    R.map (hc.desc c₀).right ≫ d.inv = inverse R c e hc ≫ R.map (hc.desc c₀).left := by
  apply (rightIsColimit R c hc).hom_ext
  intro n
  change R.map (c.ι.app n).right ≫ (R.map (hc.desc c₀).right ≫ d.inv) =
    R.map (c.ι.app n).right ≫ (inverse R c e hc ≫ R.map (hc.desc c₀).left)
  have hL : R.map (c.ι.app (n + 1)).left ≫ R.map (hc.desc c₀).left =
      R.map (c₀.ι.app (n + 1)).left := by
    rw [← R.map_comp]
    exact congrArg (fun f : D.obj (n + 1) ⟶ c₀.pt ↦ R.map f.left) (hc.fac c₀ (n + 1))
  have hR : R.map (c.ι.app n).right ≫ R.map (hc.desc c₀).right =
      R.map (c₀.ι.app n).right := by
    rw [← R.map_comp]
    exact congrArg (fun f : D.obj n ⟶ c₀.pt ↦ R.map f.right) (hc.fac c₀ n)
  rw [← Category.assoc, hR, ← Category.assoc, inverse_fac, Category.assoc, hL]
  exact (he.inverse_fac n).symm

end DaggerCountableCrossedInverseTargetSquare
