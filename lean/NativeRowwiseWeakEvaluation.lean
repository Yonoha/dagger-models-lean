import NativeMappingEvaluationRealizationUnit

/-! Actual component evaluation arrows are isomorphic along rowwise weak maps of Kan rows. -/
set_option autoImplicit false
open CategoryTheory MonoidalCategory MonoidalClosed HomotopicalAlgebra
open DaggerNativeMappingEvaluationRealizationUnit DaggerNativeIhomWeakBetweenKan
open DaggerOriginalSimplicialPiZeroWeakEquivalence DaggerOriginalFixedObjectCotensorPoints
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeRowwiseWeakEvaluation
noncomputable section

def componentMap {F G : SimplexCategoryᵒᵖ ⥤ SSet.{u}} (f : F ⟶ G) :
    F ⋙ SSet.π₀Functor ⟶ G ⋙ SSet.π₀Functor := Functor.whiskerRight f SSet.π₀Functor

def mappingComponentMap {F G : SimplexCategoryᵒᵖ ⥤ SSet.{u}} (f : F ⟶ G) (K : SSet.{u}) :
    F ⋙ ihom K ⋙ SSet.π₀Functor ⟶ G ⋙ ihom K ⋙ SSet.π₀Functor :=
  Functor.whiskerRight (Functor.whiskerRight f (ihom K)) SSet.π₀Functor

theorem componentMap_isIso {F G : SimplexCategoryᵒᵖ ⥤ SSet.{u}} (f : F ⟶ G)
    (hf : ∀ k, WeakEquivalence (f.app k)) : IsIso (componentMap f) := by
  apply (NatTrans.isIso_iff_isIso_app _).mpr
  intro k
  have := hf k
  exact (isIso_iff_bijective _).mpr (bijective_mapPiZero (f.app k))

theorem mappingComponentMap_isIso {F G : SimplexCategoryᵒᵖ ⥤ SSet.{u}}
    [∀ k, IsFibrant (F.obj k)] [∀ k, IsFibrant (G.obj k)] (f : F ⟶ G)
    (hf : ∀ k, WeakEquivalence (f.app k)) (K : SSet.{u}) :
    IsIso (mappingComponentMap f K) := by
  apply (NatTrans.isIso_iff_isIso_app _).mpr
  intro k
  have := hf k
  have : WeakEquivalence ((ihom K).map (f.app k)) := ihom_map_weak K _
  exact (isIso_iff_bijective _).mpr (bijective_mapPiZero ((ihom K).map (f.app k)))

theorem evaluation_square {F G : SimplexCategoryᵒᵖ ⥤ SSet.{u}} (f : F ⟶ G)
    {K : SSet.{u}} (a : 𝟙_ SSet.{u} ⟶ K) :
    mappingComponentMap f K ≫ rowEvaluation G a = rowEvaluation F a ≫ componentMap f := by
  apply NatTrans.ext
  funext k c
  change SSet.mapπ₀ (pointEvaluation a _)
    (SSet.mapπ₀ ((ihom K).map (f.app k)) c) =
      SSet.mapπ₀ (f.app k) (SSet.mapπ₀ (pointEvaluation a _) c)
  rw [← SSet.mapπ₀_comp_apply, pointEvaluation_natural, SSet.mapπ₀_comp_apply]

def evaluationArrowIso {F G : SimplexCategoryᵒᵖ ⥤ SSet.{u}}
    [∀ k, IsFibrant (F.obj k)] [∀ k, IsFibrant (G.obj k)] (f : F ⟶ G)
    (hf : ∀ k, WeakEquivalence (f.app k)) {K : SSet.{u}} (a : 𝟙_ SSet.{u} ⟶ K) :
    Arrow.mk (rowEvaluation F a) ≅ Arrow.mk (rowEvaluation G a) := by
  have := componentMap_isIso f hf
  have := mappingComponentMap_isIso f hf K
  exact Arrow.isoMk (asIso (mappingComponentMap f K)) (asIso (componentMap f))
    (evaluation_square f a)

theorem evaluation_fibration_iff {F G : SimplexCategoryᵒᵖ ⥤ SSet.{u}}
    [∀ k, IsFibrant (F.obj k)] [∀ k, IsFibrant (G.obj k)] (f : F ⟶ G)
    (hf : ∀ k, WeakEquivalence (f.app k)) {K : SSet.{u}} (a : 𝟙_ SSet.{u} ⟶ K) :
    Fibration (C := SSet.{u}) (rowEvaluation F a) ↔
      Fibration (C := SSet.{u}) (rowEvaluation G a) :=
  (HomotopicalAlgebra.fibration_iff _).trans
    (((fibrations SSet.{u}).arrow_mk_iso_iff (evaluationArrowIso f hf a)).trans
      (HomotopicalAlgebra.fibration_iff _).symm)

end
end DaggerNativeRowwiseWeakEvaluation
