import PresentableParameterIhomAccessibility
import RectangularInverseWitnessData
import FiniteStageHomFactors
import Mathlib.CategoryTheory.Limits.Comma

/-! Both actual endpoint colimits of the original Arrow diagram, before any stage is weak. -/
set_option autoImplicit false
open CategoryTheory Limits
open DaggerNativeJoyalWeakSimplexInverse
universe u v w
namespace DaggerOriginalArrowWitnessStageDiagrams
noncomputable section
variable {C : Type w} [Category.{v} C] {J : Type u} [SmallCategory J]
  [HasColimitsOfShape J C] (R : C ⥤ SSet.{u}) [PreservesColimitsOfShape J R]
  {F : J ⥤ Arrow C} {c : Cocone F}

abbrev leftDiagram : J ⥤ SSet.{u} := F ⋙ Arrow.leftFunc ⋙ R
abbrev rightDiagram : J ⥤ SSet.{u} := F ⋙ Arrow.rightFunc ⋙ R
abbrev leftCocone : Cocone (leftDiagram R (F := F)) :=
  R.mapCocone (Arrow.leftFunc.mapCocone c)
abbrev rightCocone : Cocone (rightDiagram R (F := F)) :=
  R.mapCocone (Arrow.rightFunc.mapCocone c)

def leftIsColimit (hc : IsColimit c) : IsColimit (leftCocone R (c := c)) :=
  isColimitOfPreserves R (isColimitOfPreserves Arrow.leftFunc hc)

def rightIsColimit (hc : IsColimit c) : IsColimit (rightCocone R (c := c)) :=
  isColimitOfPreserves R (isColimitOfPreserves Arrow.rightFunc hc)

theorem inverse_stage (κ : Cardinal.{u}) [Fact κ.IsRegular] [IsCardinalFiltered J κ]
    (hc : IsColimit c) (d : SimplexInverseData (R.map c.pt.hom)) (i : J)
    [IsCardinalPresentable (R.obj (F.obj i).right) κ] :
    ∃ (j : J) (_ : i ⟶ j) (g : R.obj (F.obj i).right ⟶ R.obj (F.obj j).left),
      g ≫ R.map (c.ι.app j).left = R.map (c.ι.app i).right ≫ d.inv := by
  let K : ULift.{u} PUnit → SSet.{u} := fun _ ↦ R.obj (F.obj i).right
  let D : ULift.{u} PUnit → J ⥤ SSet.{u} := fun _ ↦ leftDiagram R (F := F)
  let cc : ∀ a, Cocone (D a) := fun _ ↦ leftCocone R (c := c)
  obtain ⟨j, t, g, hg⟩ := DaggerFiniteStageHomFactors.all_homs κ K D cc
    (fun _ ↦ leftIsColimit R hc) (fun _ ↦ inferInstance)
    (fun _ ↦ R.map (c.ι.app i).right ≫ d.inv) i
  exact ⟨j, t, g (ULift.up PUnit.unit), hg (ULift.up PUnit.unit)⟩

end
end DaggerOriginalArrowWitnessStageDiagrams
