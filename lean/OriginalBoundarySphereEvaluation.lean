import NativePositiveBoundaryConnected
import OriginalConnectedMappingEvaluationFibration

/-! Positive boundary-sphere models have the exact original row evaluation fibrations. -/
set_option autoImplicit false
open CategoryTheory Simplicial MonoidalCategory HomotopicalAlgebra DaggerModels
open DaggerNativePositiveBoundaryConnected DaggerOriginalAmbientDaggerPiZeroGroupoid
open DaggerOriginalConnectedMappingEvaluationFibration OriginalOrdinaryLocalKanReplacement
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerOriginalBoundarySphereEvaluation
noncomputable section

def boundaryPoint (n : ℕ) : 𝟙_ SSet.{u} ⟶ (SSet.boundary (n + 2) : SSet.{u}) :=
  SSet.const (boundaryVertex (n + 1))

theorem replacement_positive_sphere_evaluation_fibrations (n : ℕ)
    (C : SimplicialCat.{u, u}) (hC : HasActualComponentGroupoid C) :
    Fibration (mappingBaseEvaluation (boundaryPoint n) (replacement.obj C)) ∧
      ∀ z : (replacement.obj C).Obj,
        Fibration (mappingBarEvaluation (boundaryPoint n) (replacement.obj C) z) :=
  replacement_evaluation_fibrations (boundaryPoint n) C hC

end
end DaggerOriginalBoundarySphereEvaluation
