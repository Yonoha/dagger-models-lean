import NativeBasedPiWeakPullback
import NativeReedyReplacementWeakMaps
import OriginalWeakTargetNativePiKan
import OriginalUnreplacedGeometricPiKan
import OriginalWholeBarRelativeReedy

/-! Actual Reedy replacements inherit native pi Kan from ordinary local Kan replacement. -/
set_option autoImplicit false
open CategoryTheory Simplicial Opposite HomotopicalAlgebra DaggerModels
open DaggerNativeBasedPiFreeEvaluationPullback DaggerNativeBasedPiWeakPullback
open DaggerNativeReedyReplacementWeakMaps DaggerOriginalWeakTargetNativePiKan
open DaggerOriginalSimplicialCategoryBarRows DaggerOriginalNerveRowChainData
open DaggerOriginalNerveLocalWeakPreservation DaggerOriginalCotensorEvaluationRowMaps
open DaggerOriginalBarRowsLocalWeakPreservation DaggerOriginalAmbientDaggerPiZeroGroupoid
open DaggerOriginalLocalKanReplacementDiagonalWeak
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerOriginalReedyNativePiKan
noncomputable section

open DaggerNativeFunctorialReedyReplacement

theorem reedy_base_native_pi_fibration (n : ℕ) (C : SimplicialCat.{u, u})
    (hC : HasActualComponentGroupoid C) :
    Fibration (basedProjection (replacement.obj (baseRows C)) (n + 1)) := by
  let D := OriginalOrdinaryLocalKanReplacement.replacement.obj C
  let f := baseRowsMap (OriginalOrdinaryLocalKanReplacement.unit.app C)
  have hf : ∀ k, WeakEquivalence (f.app k) := by
    intro k
    obtain ⟨k⟩ := k
    induction k using SimplexCategory.rec with | _ k =>
      exact baseRowsMap_weak (OriginalOrdinaryLocalKanReplacement.unit.app C)
        (OriginalOrdinaryLocalKanReplacement.unit_obj_bijective C) (unit_hom_weak C) k
  have : ∀ k, IsFibrant ((replacement.obj (baseRows C)).obj k) :=
    DaggerNativeFunctorialReedyReplacement.replacement_row_Kan _
  have : ∀ k, IsFibrant ((replacement.obj (baseRows D)).obj k) :=
    DaggerNativeFunctorialReedyReplacement.replacement_row_Kan _
  have : Fibration (basedProjection (replacement.obj (baseRows D)) (n + 1)) :=
    weak_target_base_native_pi_fibration n C hC _ (unit.app (baseRows D))
      (DaggerNativeFunctorialReedyReplacement.unit_row_weak _)
  exact basedProjection_fibration_of_rowwise_weak
    (F := replacement.obj (baseRows C)) (G := replacement.obj (baseRows D))
    (replacement.map f)
    (replacement_map_row_weak f hf) (n + 1)

theorem reedy_endpoint_bar_native_pi_fibration (n : ℕ) (C : SimplicialCat.{u, u})
    (hC : HasActualComponentGroupoid C) (z : C.Obj) :
    Fibration (basedProjection (replacement.obj (barRows C z)) (n + 1)) := by
  let D := OriginalOrdinaryLocalKanReplacement.replacement.obj C
  let w := (OriginalOrdinaryLocalKanReplacement.unit.app C).obj z
  let f := barRowsMap (OriginalOrdinaryLocalKanReplacement.unit.app C) z
  have hf : ∀ k, WeakEquivalence (f.app k) := by
    intro k
    obtain ⟨k⟩ := k
    induction k using SimplexCategory.rec with | _ k =>
      exact barRowsMap_weak (OriginalOrdinaryLocalKanReplacement.unit.app C)
        (OriginalOrdinaryLocalKanReplacement.unit_obj_bijective C) (unit_hom_weak C) z k
  have : ∀ k, IsFibrant ((replacement.obj (barRows C z)).obj k) :=
    DaggerNativeFunctorialReedyReplacement.replacement_row_Kan _
  have : ∀ k, IsFibrant ((replacement.obj (barRows D w)).obj k) :=
    DaggerNativeFunctorialReedyReplacement.replacement_row_Kan _
  have : Fibration (basedProjection (replacement.obj (barRows D w)) (n + 1)) :=
    weak_target_bar_native_pi_fibration n C hC w _ (unit.app (barRows D w))
      (DaggerNativeFunctorialReedyReplacement.unit_row_weak _)
  exact basedProjection_fibration_of_rowwise_weak
    (F := replacement.obj (barRows C z)) (G := replacement.obj (barRows D w))
    (replacement.map f)
    (replacement_map_row_weak f hf) (n + 1)

theorem whole_bar_replaced_base_native_pi_fibration (n : ℕ) (C : SimplicialCat.{u, u})
    (hC : HasActualComponentGroupoid C) : Fibration
      (basedProjection (DaggerOriginalWholeBarRelativeReedy.replacedBar C).right (n + 1)) :=
  reedy_base_native_pi_fibration n C hC

end
end DaggerOriginalReedyNativePiKan
