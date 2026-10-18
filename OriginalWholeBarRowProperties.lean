import NativeBisimplicialCoproductRows
import OriginalWholeBarBisimplicial
import OriginalWeakTargetNativePiKan
import OriginalBarRowsLocalWeakPreservation

/-! All original whole-bar rows preserve weak local maps and local-Kan row properties. -/
set_option autoImplicit false
open CategoryTheory Limits Simplicial Opposite HomotopicalAlgebra DaggerModels
open DaggerOriginalWholeBarBisimplicial DaggerOriginalSimplicialCategoryBarRows
open DaggerNativeBisimplicialCoproductRows DaggerOriginalCotensorEvaluationRowMaps
open DaggerOriginalBarRowsLocalWeakPreservation DaggerOriginalWeakTargetNativePiKan
open DaggerNativeUnitalMultiplicationAction DaggerOriginalWholeRowLoopActions
open DaggerOriginalAmbientDaggerPiZeroGroupoid DaggerOriginalPiZeroGroupoidLocalWeakInvariance
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerOriginalWholeBarRowProperties
noncomputable section

theorem wholeRowsMap_row_weak {C D : SimplicialCat.{u, u}} (F : C ⟶ D)
    (hO : Function.Bijective F.obj)
    (hF : ∀ x y : C.Obj, WeakEquivalence (F.map x y)) (h : SimplexCategoryᵒᵖ) :
    WeakEquivalence ((wholeRowsMap F).app h) := by
  change WeakEquivalence ((Limits.Sigma.map' F.obj (fun z ↦ barRowsMap F z)).app h)
  apply row_map'_weak (F := barRows C) (G := barRows D) F.obj hO
  intro z k
  obtain ⟨k⟩ := k
  induction k using SimplexCategory.rec with | _ k =>
    exact barRowsMap_weak F hO hF z k

instance replacement_whole_rows_Kan (C : SimplicialCat.{u, u})
    (h : SimplexCategoryᵒᵖ) : IsFibrant
      ((wholeRows (OriginalOrdinaryLocalKanReplacement.replacement.obj C)).obj h) := by
  have : ∀ z k, IsFibrant
      ((barRows (OriginalOrdinaryLocalKanReplacement.replacement.obj C) z).obj k) :=
    fun z ↦ replacement_bar_rows_fibrant C z
  exact coproduct_rows_Kan _ h

theorem replacement_whole_row_actions_trivial (C : SimplicialCat.{u, u})
    (hC : HasActualComponentGroupoid C) (h : SimplexCategoryᵒᵖ) :
    ∀ x, TrivialActionAt
      ((wholeRows (OriginalOrdinaryLocalKanReplacement.replacement.obj C)).obj h) x := by
  let D := OriginalOrdinaryLocalKanReplacement.replacement.obj C
  have : ∀ z k, IsFibrant ((barRows D z).obj k) :=
    fun z ↦ replacement_bar_rows_fibrant C z
  have : ∀ x y : D.Obj, IsFibrant (D.enriched.Hom x y) :=
    OriginalOrdinaryLocalKanReplacement.replacement_locallyKan C
  apply coproduct_row_actions_trivial (barRows D)
  intro z k
  obtain ⟨k⟩ := k
  induction k using SimplexCategory.rec with | _ k =>
    exact bar_row_actions_trivial D ((replacement_groupoid_iff C).mp hC) z k

end
end DaggerOriginalWholeBarRowProperties
