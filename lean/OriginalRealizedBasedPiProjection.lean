import NativeBasedPiProjectionFibration
import NativeChosenSphereFreeFibre
import OriginalGeometricSphereEvaluationFibration
import OriginalWholeRowLoopActions

/-! Original R(C) realized rows satisfy literal based-pi horn lifting over all singular vertices. -/
set_option autoImplicit false
open CategoryTheory MonoidalCategory Simplicial HomotopicalAlgebra DaggerModels
open DaggerNativeBasedPiFreeEvaluationPullback DaggerNativeBasedPiProjectionFibration
open DaggerNativeChosenSphereFreeFibre DaggerNativeMappingEvaluationRealizationUnit
open DaggerNativePositiveBoundaryConnected DaggerOriginalSimplicialCategoryBarRows
open DaggerOriginalWholeRowLoopActions DaggerOriginalAmbientDaggerPiZeroGroupoid
open DaggerOriginalBoundarySphereEvaluation DaggerNativeUnitalMultiplicationAction
open OriginalOrdinaryLocalKanReplacement
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerOriginalRealizedBasedPiProjection
noncomputable section

theorem replacement_realized_base_based_pi_fibration (n : ℕ) (C : SimplicialCat.{u, u})
    (hC : HasActualComponentGroupoid C) :
    Fibration (basedProjection (baseRows (replacement.obj C) ⋙
      (SSet.toTop ⋙ TopCat.toSSet)) (n + 1)) := by
  let F := baseRows (replacement.obj C)
  have : ∀ x y : (replacement.obj C).Obj,
      IsFibrant ((replacement.obj C).enriched.Hom x y) := replacement_locallyKan C
  have : ∀ k, IsFibrant (F.obj k) := by
    intro k
    obtain ⟨k⟩ := k
    induction k using SimplexCategory.rec with | _ k =>
      exact base_row_fibrant (replacement.obj C) k
  have : ∀ k, IsFibrant ((F ⋙ (SSet.toTop ⋙ TopCat.toSSet)).obj k) := by
    intro k
    change IsFibrant (TopCat.toSSet.obj (SSet.toTop.obj (F.obj k)))
    infer_instance
  have hs : ∀ k x, TrivialActionAt ((F ⋙ (SSet.toTop ⋙ TopCat.toSSet)).obj k) x := by
    intro k
    obtain ⟨k⟩ := k
    induction k using SimplexCategory.rec with | _ k =>
      exact replacement_realized_base_row_actions_trivial C hC k
  have : Fibration (C := SSet.{u})
      (rowEvaluation F (SSet.const (boundaryVertex (n + 1)))) :=
    (replacement_positive_sphere_evaluation_fibrations n C hC).1
  have : Fibration (C := SSet.{u}) (rowEvaluation (F ⋙ (SSet.toTop ⋙ TopCat.toSSet))
      (chosenHornPoint (n + 1) ≫ SSet.Subcomplex.homOfLE (SSet.horn_le_boundary 0))) := by
    rw [chosenHornPoint_comp_boundary]
    exact realized_evaluation_fibration F (SSet.const (boundaryVertex (n + 1)))
  exact basedProjection_fibration _ (n + 1) 0 (chosenHornPoint (n + 1)) hs

theorem replacement_realized_bar_based_pi_fibration (n : ℕ) (C : SimplicialCat.{u, u})
    (hC : HasActualComponentGroupoid C) (z : (replacement.obj C).Obj) :
    Fibration (basedProjection (barRows (replacement.obj C) z ⋙
      (SSet.toTop ⋙ TopCat.toSSet)) (n + 1)) := by
  let F := barRows (replacement.obj C) z
  have : ∀ x y : (replacement.obj C).Obj,
      IsFibrant ((replacement.obj C).enriched.Hom x y) := replacement_locallyKan C
  have : ∀ k, IsFibrant (F.obj k) := by
    intro k
    obtain ⟨k⟩ := k
    induction k using SimplexCategory.rec with | _ k =>
      exact bar_row_fibrant (replacement.obj C) z k
  have : ∀ k, IsFibrant ((F ⋙ (SSet.toTop ⋙ TopCat.toSSet)).obj k) := by
    intro k
    change IsFibrant (TopCat.toSSet.obj (SSet.toTop.obj (F.obj k)))
    infer_instance
  have hs : ∀ k x, TrivialActionAt ((F ⋙ (SSet.toTop ⋙ TopCat.toSSet)).obj k) x := by
    intro k
    obtain ⟨k⟩ := k
    induction k using SimplexCategory.rec with | _ k =>
      exact replacement_realized_bar_row_actions_trivial C hC z k
  have : Fibration (C := SSet.{u})
      (rowEvaluation F (SSet.const (boundaryVertex (n + 1)))) :=
    (replacement_positive_sphere_evaluation_fibrations n C hC).2 z
  have : Fibration (C := SSet.{u}) (rowEvaluation (F ⋙ (SSet.toTop ⋙ TopCat.toSSet))
      (chosenHornPoint (n + 1) ≫ SSet.Subcomplex.homOfLE (SSet.horn_le_boundary 0))) := by
    rw [chosenHornPoint_comp_boundary]
    exact realized_evaluation_fibration F (SSet.const (boundaryVertex (n + 1)))
  exact basedProjection_fibration _ (n + 1) 0 (chosenHornPoint (n + 1)) hs

end
end DaggerOriginalRealizedBasedPiProjection
