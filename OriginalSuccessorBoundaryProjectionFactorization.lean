import OriginalSuccessorBoundaryRestLifting

/-!
# Exact factorization of the original successor boundary projection

The first-face restriction retains the original suffix projection. The cone
transpose commutes with the original whole-overlap restriction, hence gives
an exact factorization of the successor boundary projection through the
remaining mapping presheaf and B_k(J_0 X). No invertibility of the cone
transpose, nor full higher-prefix boundary lifting, is assumed or claimed.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerOriginalSimplexCoslice DaggerOriginalJoinedHornGeometry
open DaggerOriginalJoinedBoundaryRestriction DaggerOriginalJoinedBoundaryProjection
open DaggerOriginalJoinedBoundarySuffixInclusion
open DaggerOriginalPrefixDeleteFirstCoface DaggerOriginalPrefixDeleteFirstNativeJoin
open DaggerOriginalPrefixBoundarySuccessorMappingPullback
open DaggerOriginalZeroJoinYonedaCorrespondence
open DaggerOriginalPrefixBoundaryConeTransposition
open DaggerOriginalSuccessorBoundaryNaturalInclusions
open DaggerOriginalSuccessorBoundaryPresheafPullback

universe u

namespace DaggerOriginalSuccessorBoundaryProjectionFactorization

noncomputable section

/-- The original first-prefix coface retains every vertex of the original suffix block. -/
theorem suffix_comp_prefixDeleteFirstOperator (k : ℕ) (d : SimplexCategory) :
    AugmentedSimplexCategory.inr' ⦋k⦌ d ≫ prefixDeleteFirstOperator k d.len =
      AugmentedSimplexCategory.inr' ⦋k + 1⦌ d := by
  induction d using SimplexCategory.rec with | h d =>
    simp only [SimplexCategory.len_mk]
    rw [prefixDeleteFirstOperator_eq_native]
    have h := AugmentedSimplexCategory.inr_comp_tensorHom
      (show WithInitial.of ⦋k⦌ ⟶ WithInitial.of ⦋k + 1⦌ from SimplexCategory.δ 0)
      (𝟙 (WithInitial.of ⦋d⦌))
    change AugmentedSimplexCategory.inr' ⦋k⦌ ⦋d⦌ ≫ nativePrefixDeleteFirst k d =
      𝟙 ⦋d⦌ ≫ AugmentedSimplexCategory.inr' ⦋k + 1⦌ ⦋d⦌ at h
    simpa only [Category.id_comp] using h

/-- The first-face inclusion retains exactly the original successor suffix inclusion. -/
theorem suffix_comp_firstFaceBoundaryInclusion (k : ℕ) (d : SimplexCategory) :
    SSet.stdSimplex.map (AugmentedSimplexCategory.inr' ⦋k⦌ d) ≫
        firstFaceBoundaryInclusion.{u} k d.len =
      boundarySuffixInclusion (k + 1) d := by
  apply (cancel_mono (prefixBoundary (k + 1) d.len).ι).mp
  rw [Category.assoc, firstFaceBoundaryInclusion_comp_inclusion,
    boundarySuffixInclusion_comp (k + 1) d]
  dsimp only [prefixDeleteFirstMap]
  rw [← Functor.map_comp, suffix_comp_prefixDeleteFirstOperator]

/-- Restriction to the first face followed by the original suffix projection is the original
successor boundary projection itself. -/
theorem successorFirstRestriction_comp_projection (k : ℕ) (X : SSet.{u}) :
    successorFirstRestriction k X ≫ suffixProjection ⦋k⦌ X =
      boundaryProjection (k + 1) X := by
  ext q g
  change X.map (AugmentedSimplexCategory.inr' ⦋k⦌ q.unop).op
      (SSet.yonedaEquiv (firstFaceBoundaryInclusion k q.unop.len ≫ g)) =
    SSet.yonedaEquiv (boundarySuffixInclusion (k + 1) q.unop ≫ g)
  rw [← yonedaEquiv_precomp_actual, ← Category.assoc,
    suffix_comp_firstFaceBoundaryInclusion]

/-- Postcompose each actual original whole-boundary map with the same original target map. -/
def boundaryPostcompose (k : ℕ) {X Y : SSet.{u}} (p : X ⟶ Y) :
    boundaryJoinedPresheaf k X ⟶ boundaryJoinedPresheaf k Y where
  app q g := g ≫ p
  naturality a b β := by
    funext g
    change (DaggerOriginalJoinedPrefixBoundaryFunctor.prefixBoundaryMap k β.unop ≫ g) ≫
        p = DaggerOriginalJoinedPrefixBoundaryFunctor.prefixBoundaryMap k β.unop ≫ (g ≫ p)
    exact Category.assoc _ g p

/-- Whole-boundary projection commutes with the actual target map. -/
theorem boundaryPostcompose_comp_projection (k : ℕ) {X Y : SSet.{u}} (p : X ⟶ Y) :
    boundaryPostcompose k p ≫ boundaryProjection k Y = boundaryProjection k X ≫ p := by
  ext q g
  change SSet.yonedaEquiv (boundarySuffixInclusion k q.unop ≫ (g ≫ p)) =
    p.app q (SSet.yonedaEquiv (boundarySuffixInclusion k q.unop ≫ g))
  rw [← Category.assoc, SSet.yonedaEquiv_comp]

/-- The cone transpose commutes with the exact original whole-overlap restriction. -/
theorem restConeTransposition_comp_postcompose (k : ℕ) (X : SSet.{u}) :
    restBoundaryConeTransposition k X ≫ boundaryPostcompose k (suffixProjection ⦋0⦌ X) =
      restOverlapRestriction k X := by
  ext q g
  exact prefixConeTranspose_comp_suffix k q.unop.len g

/-- The cone transpose retains the original smaller whole-boundary and vertex projections. -/
theorem restConeTransposition_comp_projection (k : ℕ) (X : SSet.{u}) :
    restBoundaryConeTransposition k X ≫ boundaryProjection k (joinedPresheaf ⦋0⦌ X) ≫
        suffixProjection ⦋0⦌ X =
      restOverlapRestriction k X ≫ boundaryProjection k X := by
  rw [← boundaryPostcompose_comp_projection, ← Category.assoc,
    restConeTransposition_comp_postcompose]

/-- The actual original successor boundary projection has the exact cone-route factorization.
-/
theorem successorBoundaryProjection_factorization (k : ℕ) (X : SSet.{u}) :
    successorRestRestriction k X ≫ restBoundaryConeTransposition k X ≫
        boundaryProjection k (joinedPresheaf ⦋0⦌ X) ≫ suffixProjection ⦋0⦌ X =
      boundaryProjection (k + 1) X := by
  rw [restConeTransposition_comp_projection, ← Category.assoc,
    ← successorBoundaryRestriction_square, Category.assoc,
    joinedBoundaryRestriction_comp_projection, successorFirstRestriction_comp_projection]

end

end DaggerOriginalSuccessorBoundaryProjectionFactorization
