import NativeWeakRowBasedPiTransfer
import NativeChosenSphereFreeFibre
import OriginalBoundarySphereEvaluation
import OriginalWholeRowLoopActions

/-! Forward weak targets of the exact original R(C) rows satisfy literal native pi Kan. -/
set_option autoImplicit false
open CategoryTheory Simplicial Opposite HomotopicalAlgebra DaggerModels
open DaggerNativeWeakRowBasedPiTransfer DaggerNativeBasedPiFreeEvaluationPullback
open DaggerNativeMappingEvaluationRealizationUnit DaggerNativeUnitalMultiplicationAction
open DaggerNativeChosenSphereFreeFibre DaggerNativePositiveBoundaryConnected
open DaggerOriginalBoundarySphereEvaluation DaggerOriginalWholeRowLoopActions
open DaggerOriginalSimplicialCategoryBarRows DaggerOriginalAmbientDaggerPiZeroGroupoid
open DaggerOriginalPiZeroGroupoidLocalWeakInvariance OriginalOrdinaryLocalKanReplacement
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerOriginalWeakTargetNativePiKan
noncomputable section

theorem replacement_base_rows_fibrant (C : SimplicialCat.{u, u}) :
    ∀ k, IsFibrant ((baseRows (replacement.obj C)).obj k) := by
  have : ∀ x y : (replacement.obj C).Obj,
      IsFibrant ((replacement.obj C).enriched.Hom x y) := replacement_locallyKan C
  intro k
  obtain ⟨k⟩ := k
  induction k using SimplexCategory.rec with | _ k =>
    exact base_row_fibrant (replacement.obj C) k

theorem replacement_bar_rows_fibrant (C : SimplicialCat.{u, u})
    (z : (replacement.obj C).Obj) :
    ∀ k, IsFibrant ((barRows (replacement.obj C) z).obj k) := by
  have : ∀ x y : (replacement.obj C).Obj,
      IsFibrant ((replacement.obj C).enriched.Hom x y) := replacement_locallyKan C
  intro k
  obtain ⟨k⟩ := k
  induction k using SimplexCategory.rec with | _ k =>
    exact bar_row_fibrant (replacement.obj C) z k

theorem weak_target_base_native_pi_fibration (n : ℕ) (C : SimplicialCat.{u, u})
    (hC : HasActualComponentGroupoid C) (G : SimplexCategoryᵒᵖ ⥤ SSet.{u})
    [∀ k, IsFibrant (G.obj k)] (f : baseRows (replacement.obj C) ⟶ G)
    (hf : ∀ k, WeakEquivalence (f.app k)) : Fibration (basedProjection G (n + 1)) := by
  let F := baseRows (replacement.obj C)
  have : ∀ x y : (replacement.obj C).Obj,
      IsFibrant ((replacement.obj C).enriched.Hom x y) := replacement_locallyKan C
  have : ∀ k, IsFibrant (F.obj k) := replacement_base_rows_fibrant C
  have hs : ∀ k x, TrivialActionAt (F.obj k) x := by
    intro k
    obtain ⟨k⟩ := k
    induction k using SimplexCategory.rec with | _ k =>
      exact base_row_actions_trivial (replacement.obj C) ((replacement_groupoid_iff C).mp hC) k
  have he : Fibration (C := SSet.{u})
      (rowEvaluation F (SSet.const (boundaryVertex (n + 1)))) :=
    (replacement_positive_sphere_evaluation_fibrations n C hC).1
  have hh : Fibration (C := SSet.{u}) (rowEvaluation F
      (chosenHornPoint (n + 1) ≫ SSet.Subcomplex.homOfLE (SSet.horn_le_boundary 0))) := by
    rw [chosenHornPoint_comp_boundary]
    exact he
  exact target_basedProjection_fibration f hf (n + 1) 0 (chosenHornPoint (n + 1)) hs hh

theorem weak_target_bar_native_pi_fibration (n : ℕ) (C : SimplicialCat.{u, u})
    (hC : HasActualComponentGroupoid C) (z : (replacement.obj C).Obj)
    (G : SimplexCategoryᵒᵖ ⥤ SSet.{u}) [∀ k, IsFibrant (G.obj k)]
    (f : barRows (replacement.obj C) z ⟶ G) (hf : ∀ k, WeakEquivalence (f.app k)) :
    Fibration (basedProjection G (n + 1)) := by
  let F := barRows (replacement.obj C) z
  have : ∀ x y : (replacement.obj C).Obj,
      IsFibrant ((replacement.obj C).enriched.Hom x y) := replacement_locallyKan C
  have : ∀ k, IsFibrant (F.obj k) := replacement_bar_rows_fibrant C z
  have hs : ∀ k x, TrivialActionAt (F.obj k) x := by
    intro k
    obtain ⟨k⟩ := k
    induction k using SimplexCategory.rec with | _ k =>
      exact bar_row_actions_trivial (replacement.obj C)
        ((replacement_groupoid_iff C).mp hC) z k
  have he : Fibration (C := SSet.{u})
      (rowEvaluation F (SSet.const (boundaryVertex (n + 1)))) :=
    (replacement_positive_sphere_evaluation_fibrations n C hC).2 z
  have hh : Fibration (C := SSet.{u}) (rowEvaluation F
      (chosenHornPoint (n + 1) ≫ SSet.Subcomplex.homOfLE (SSet.horn_le_boundary 0))) := by
    rw [chosenHornPoint_comp_boundary]
    exact he
  exact target_basedProjection_fibration f hf (n + 1) 0 (chosenHornPoint (n + 1)) hs hh

theorem replacement_base_native_pi_fibration (n : ℕ) (C : SimplicialCat.{u, u})
    (hC : HasActualComponentGroupoid C) :
    Fibration (basedProjection (baseRows (replacement.obj C)) (n + 1)) := by
  have := replacement_base_rows_fibrant C
  exact weak_target_base_native_pi_fibration n C hC _ (𝟙 _) (fun _ ↦ inferInstance)

theorem replacement_bar_native_pi_fibration (n : ℕ) (C : SimplicialCat.{u, u})
    (hC : HasActualComponentGroupoid C) (z : (replacement.obj C).Obj) :
    Fibration (basedProjection (barRows (replacement.obj C) z) (n + 1)) := by
  have := replacement_bar_rows_fibrant C z
  exact weak_target_bar_native_pi_fibration n C hC z _ (𝟙 _) (fun _ ↦ inferInstance)

end
end DaggerOriginalWeakTargetNativePiKan
