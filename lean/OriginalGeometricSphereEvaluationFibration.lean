import NativeGeometricSphereRowEvaluation
import OriginalBoundarySphereEvaluation
import OriginalWholeRowLoopActions

/-! Actual geometric positive sphere evaluation is a Kan fibration on both original R(C) rows. -/
set_option autoImplicit false
open CategoryTheory Simplicial HomotopicalAlgebra DaggerModels
open DaggerNativeGeometricSphereRowEvaluation DaggerNativePositiveBoundaryConnected
open DaggerOriginalSimplicialCategoryBarRows DaggerOriginalAmbientDaggerPiZeroGroupoid
open DaggerOriginalWholeRowLoopActions DaggerNativeMappingEvaluationRealizationUnit
open DaggerOriginalBoundarySphereEvaluation DaggerOriginalConnectedMappingEvaluationFibration
open OriginalOrdinaryLocalKanReplacement
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerOriginalGeometricSphereEvaluationFibration
noncomputable section

def baseSphereEvaluation (n : ℕ) (C : SimplicialCat.{u, u}) :=
  geometricRowEvaluation (baseRows C) (n + 1) (boundaryVertex (n + 1))

def barSphereEvaluation (n : ℕ) (C : SimplicialCat.{u, u}) (z : C.Obj) :=
  geometricRowEvaluation (barRows C z) (n + 1) (boundaryVertex (n + 1))

theorem replacement_base_sphere_evaluation_fibration (n : ℕ)
    (C : SimplicialCat.{u, u}) (hC : HasActualComponentGroupoid C) :
    Fibration (C := SSet.{u}) (baseSphereEvaluation n (replacement.obj C)) := by
  letI : ∀ x y : (replacement.obj C).Obj,
      IsFibrant ((replacement.obj C).enriched.Hom x y) := replacement_locallyKan C
  have : ∀ k, IsFibrant ((baseRows (replacement.obj C)).obj k) := by
    intro k
    obtain ⟨k⟩ := k
    induction k using SimplexCategory.rec with | _ k =>
      exact base_row_fibrant (replacement.obj C) k
  have : Fibration (C := SSet.{u})
      (rowEvaluation (baseRows (replacement.obj C))
        (SSet.const (boundaryVertex (n + 1)))) :=
    (replacement_positive_sphere_evaluation_fibrations n C hC).1
  exact geometric_row_evaluation_fibration _ (n + 1) (boundaryVertex (n + 1))

theorem replacement_bar_sphere_evaluation_fibration (n : ℕ)
    (C : SimplicialCat.{u, u}) (hC : HasActualComponentGroupoid C)
    (z : (replacement.obj C).Obj) :
    Fibration (C := SSet.{u}) (barSphereEvaluation n (replacement.obj C) z) := by
  letI : ∀ x y : (replacement.obj C).Obj,
      IsFibrant ((replacement.obj C).enriched.Hom x y) := replacement_locallyKan C
  have : ∀ k, IsFibrant ((barRows (replacement.obj C) z).obj k) := by
    intro k
    obtain ⟨k⟩ := k
    induction k using SimplexCategory.rec with | _ k =>
      exact bar_row_fibrant (replacement.obj C) z k
  have : Fibration (C := SSet.{u})
      (rowEvaluation (barRows (replacement.obj C) z)
        (SSet.const (boundaryVertex (n + 1)))) :=
    (replacement_positive_sphere_evaluation_fibrations n C hC).2 z
  exact geometric_row_evaluation_fibration _ (n + 1) (boundaryVertex (n + 1))

theorem replacement_geometric_sphere_evaluation_fibrations (n : ℕ)
    (C : SimplicialCat.{u, u}) (hC : HasActualComponentGroupoid C) :
    Fibration (C := SSet.{u}) (baseSphereEvaluation n (replacement.obj C)) ∧
      ∀ z : (replacement.obj C).Obj,
        Fibration (C := SSet.{u}) (barSphereEvaluation n (replacement.obj C) z) :=
  ⟨replacement_base_sphere_evaluation_fibration n C hC,
    replacement_bar_sphere_evaluation_fibration n C hC⟩

end
end DaggerOriginalGeometricSphereEvaluationFibration
