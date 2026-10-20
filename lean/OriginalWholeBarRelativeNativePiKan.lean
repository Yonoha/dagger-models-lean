import OriginalWholeBarRowProperties
import NativeCoproductEvaluationFibration
import NativeReedyReplacementWeakMaps
import NativeBasedPiWeakPullback
import OriginalWholeBarRelativeReedy
import OriginalLocalKanReplacementDiagonalWeak

/-! The SAME whole-bar relative replacement has native pi Kan in every positive degree. -/
set_option autoImplicit false
open CategoryTheory Simplicial Opposite HomotopicalAlgebra MonoidalCategory DaggerModels
open DaggerOriginalWholeBarBisimplicial DaggerOriginalWholeBarRelativeReedy
open DaggerOriginalWholeBarRowProperties DaggerOriginalSimplicialCategoryBarRows
open DaggerNativeBasedPiFreeEvaluationPullback DaggerNativeWeakRowBasedPiTransfer
open DaggerNativeMappingEvaluationRealizationUnit DaggerNativeCoproductEvaluationFibration
open DaggerNativePositiveBoundaryConnected DaggerNativeChosenSphereFreeFibre
open DaggerOriginalBoundarySphereEvaluation DaggerOriginalAmbientDaggerPiZeroGroupoid
open DaggerNativeReedyReplacementWeakMaps DaggerNativeBasedPiWeakPullback
open DaggerOriginalLocalKanReplacementDiagonalWeak
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerOriginalWholeBarRelativeNativePiKan
noncomputable section

theorem whole_weak_target_native_pi_fibration (n : ℕ) (C : SimplicialCat.{u, u})
    (hC : HasActualComponentGroupoid C) (G : SimplexCategoryᵒᵖ ⥤ SSet.{u})
    [∀ h, IsFibrant (G.obj h)]
    (f : wholeRows (OriginalOrdinaryLocalKanReplacement.replacement.obj C) ⟶ G)
    (hf : ∀ h, WeakEquivalence (f.app h)) : Fibration (basedProjection G (n + 1)) := by
  let D := OriginalOrdinaryLocalKanReplacement.replacement.obj C
  let F := wholeRows D
  have : ∀ h, IsFibrant (F.obj h) := replacement_whole_rows_Kan C
  have he : Fibration (C := SSet.{u})
      (rowEvaluation F (SSet.const (boundaryVertex (n + 1)))) := by
    have : ∀ z, Fibration (C := SSet.{u})
        (rowEvaluation (barRows D z) (SSet.const (boundaryVertex (n + 1)))) :=
      (replacement_positive_sphere_evaluation_fibrations n C hC).2
    exact coproduct_evaluation_fibration (barRows D) (boundaryVertex (n + 1)) _
  have hh : Fibration (C := SSet.{u}) (rowEvaluation F
      (chosenHornPoint (n + 1) ≫ SSet.Subcomplex.homOfLE (SSet.horn_le_boundary 0))) := by
    rw [chosenHornPoint_comp_boundary]
    exact he
  exact target_basedProjection_fibration f hf (n + 1) 0 (chosenHornPoint (n + 1))
    (replacement_whole_row_actions_trivial C hC) hh

theorem replaced_local_whole_native_pi_fibration (n : ℕ) (C : SimplicialCat.{u, u})
    (hC : HasActualComponentGroupoid C) : Fibration (basedProjection
      (replacedBar (OriginalOrdinaryLocalKanReplacement.replacement.obj C)).left (n + 1)) := by
  let D := OriginalOrdinaryLocalKanReplacement.replacement.obj C
  have : ∀ h, IsFibrant ((replacedBar D).left.obj h) := bar_total_rows_Kan D
  exact whole_weak_target_native_pi_fibration n C hC _
    (DaggerNativeReedyRelativeReplacement.totalUnit (barArrow D)) (fun h ↦
      ((mem_trivialCofibrations_iff _).mp
        (DaggerNativeReedyRelativeReplacement.totalUnit_row_trivial (barArrow D) h)).2)

theorem replaced_whole_native_pi_fibration (n : ℕ) (C : SimplicialCat.{u, u})
    (hC : HasActualComponentGroupoid C) :
    Fibration (basedProjection (replacedBar C).left (n + 1)) := by
  let D := OriginalOrdinaryLocalKanReplacement.replacement.obj C
  let u := OriginalOrdinaryLocalKanReplacement.unit.app C
  have hleft : ∀ h, WeakEquivalence ((wholeRowsMap u).app h) :=
    wholeRowsMap_row_weak u (OriginalOrdinaryLocalKanReplacement.unit_obj_bijective C)
      (unit_hom_weak C)
  have hf : ∀ h, WeakEquivalence ((replacedBarMap u).left.app h) :=
    relative_total_map_row_weak (barArrowMap u) hleft
  have : ∀ h, IsFibrant ((replacedBar C).left.obj h) := bar_total_rows_Kan C
  have : ∀ h, IsFibrant ((replacedBar D).left.obj h) := bar_total_rows_Kan D
  have := replaced_local_whole_native_pi_fibration n C hC
  exact basedProjection_fibration_of_rowwise_weak
    (F := (replacedBar C).left) (G := (replacedBar D).left)
    (replacedBarMap u).left hf (n + 1)

end
end DaggerOriginalWholeBarRelativeNativePiKan
