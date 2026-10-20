import RelativeInverseLadderData
import Mathlib.CategoryTheory.Limits.Comma

/-! Both actual endpoints of a countable original Arrow colimit. -/
set_option autoImplicit false
open CategoryTheory Limits
universe u v w
namespace DaggerCountableArrowStageDiagrams
noncomputable section
variable {C : Type w} [Category.{v} C] [HasColimitsOfShape ℕ C]
  (R : C ⥤ SSet.{u}) [PreservesColimitsOfShape ℕ R]
  {D : ℕ ⥤ Arrow C} (c : Cocone D)

abbrev leftDiagram : ℕ ⥤ SSet.{u} := D ⋙ Arrow.leftFunc ⋙ R
abbrev rightDiagram : ℕ ⥤ SSet.{u} := D ⋙ Arrow.rightFunc ⋙ R
abbrev leftCocone : Cocone (leftDiagram R (D := D)) := R.mapCocone (Arrow.leftFunc.mapCocone c)
abbrev rightCocone : Cocone (rightDiagram R (D := D)) := R.mapCocone (Arrow.rightFunc.mapCocone c)

def leftIsColimit (hc : IsColimit c) : IsColimit (leftCocone R c) :=
  isColimitOfPreserves R (isColimitOfPreserves Arrow.leftFunc hc)

def rightIsColimit (hc : IsColimit c) : IsColimit (rightCocone R c) :=
  isColimitOfPreserves R (isColimitOfPreserves Arrow.rightFunc hc)

omit [HasColimitsOfShape ℕ C] [PreservesColimitsOfShape ℕ R] in
theorem left_leg (n : ℕ) :
    R.map (DaggerRelativeInverseLadderData.step D n).left ≫ R.map (c.ι.app (n + 1)).left =
      R.map (c.ι.app n).left := by
  rw [← R.map_comp]
  exact congrArg (fun p : D.obj n ⟶ c.pt ↦ R.map p.left) (c.w (homOfLE (n.le_add_right 1)))

omit [HasColimitsOfShape ℕ C] [PreservesColimitsOfShape ℕ R] in
theorem right_leg (n : ℕ) :
    R.map (DaggerRelativeInverseLadderData.step D n).right ≫ R.map (c.ι.app (n + 1)).right =
      R.map (c.ι.app n).right := by
  rw [← R.map_comp]
  exact congrArg (fun p : D.obj n ⟶ c.pt ↦ R.map p.right) (c.w (homOfLE (n.le_add_right 1)))

end
end DaggerCountableArrowStageDiagrams
