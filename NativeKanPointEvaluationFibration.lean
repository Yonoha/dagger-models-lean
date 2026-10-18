import NativePointEvaluationMappingFibreIso
import TopCatModelCategory.ModelCategorySSet

/-! Actual point evaluation on a native internal Hom into a Kan target is a Kan fibration. -/
set_option autoImplicit false
open CategoryTheory MonoidalCategory MonoidalClosed HomotopicalAlgebra
open DaggerOriginalFixedObjectCotensorPoints
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeKanPointEvaluationFibration

instance pointEvaluation_fibration {D : SSet.{u}} (a : 𝟙_ SSet.{u} ⟶ D)
    (X : SSet.{u}) [IsFibrant X] : Fibration (pointEvaluation a X) := by
  have : Fibration ((MonoidalClosed.pre a).app X) := inferInstance
  have h : Fibration ((MonoidalClosed.pre a).app X ≫
      pointEvaluation (𝟙 (𝟙_ SSet.{u})) X) := inferInstance
  simpa only [pointEvaluation_parameter, Category.id_comp] using h

end DaggerNativeKanPointEvaluationFibration
