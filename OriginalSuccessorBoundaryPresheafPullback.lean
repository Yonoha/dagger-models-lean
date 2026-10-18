import OriginalSuccessorBoundaryNaturalInclusions

/-!
# The actual successor-boundary restriction square of simplicial sets

Assemble the original pointwise mapping pullbacks using the proved original
operator naturality. The first-face component retains original Yoneda and
the native joined-boundary restriction. Evaluation jointly reflects limits,
so this is an actual presheaf pullback, without any cone bijectivity premise.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial Limits
open DaggerOriginalOrdinalJoinLeft DaggerOriginalSimplexCoslice
open DaggerOriginalJoinedHornGeometry DaggerOriginalJoinedHornPrefix
open DaggerOriginalJoinedBoundaryRestriction
open DaggerOriginalPrefixBoundarySuccessorIsomorphisms
open DaggerOriginalPrefixBoundarySuccessorMappingPullback
open DaggerOriginalPrefixBoundaryConeTransposition
open DaggerOriginalSuccessorBoundaryNaturalInclusions

universe u

namespace DaggerOriginalSuccessorBoundaryPresheafPullback

noncomputable section

/-- Restrict an actual successor-boundary map to its original first prefix face. -/
def successorFirstRestriction (k : ℕ) (X : SSet.{u}) :
    boundaryJoinedPresheaf (k + 1) X ⟶ joinedPresheaf ⦋k⦌ X where
  app q g := (SSet.yonedaEquiv (X := X) (n := ⦋k + q.unop.len + 1⦌))
    (firstFaceBoundaryInclusion k q.unop.len ≫ g)
  naturality a b β := by
    funext g
    change SSet.yonedaEquiv (firstFaceBoundaryInclusion k b.unop.len ≫
        (DaggerOriginalJoinedPrefixBoundaryFunctor.prefixBoundaryMap (k + 1) β.unop ≫ g)) =
      X.map ((ordinalJoinLeft ⦋k⦌).map β.unop).op
        (SSet.yonedaEquiv (firstFaceBoundaryInclusion k a.unop.len ≫ g))
    rw [← Category.assoc, ← firstFaceBoundaryInclusion_naturality, Category.assoc]
    exact DaggerOriginalZeroJoinYonedaCorrespondence.yonedaEquiv_precomp_actual _ _

/-- Restrict an actual successor-boundary map to the original remaining prefix faces. -/
def successorRestRestriction (k : ℕ) (X : SSet.{u}) :
    boundaryJoinedPresheaf (k + 1) X ⟶ restBoundaryJoinedPresheaf k X where
  app q g := restBoundaryInclusion k q.unop.len ≫ g
  naturality a b β := by
    funext g
    change restBoundaryInclusion k b.unop.len ≫
        (DaggerOriginalJoinedPrefixBoundaryFunctor.prefixBoundaryMap (k + 1) β.unop ≫ g) =
      DaggerOriginalRestPrefixBoundaryFunctor.restPrefixBoundaryMap k β.unop ≫
        (restBoundaryInclusion k a.unop.len ≫ g)
    rw [← Category.assoc, ← restBoundaryInclusion_naturality, Category.assoc]

/-- Restrict a remaining-boundary map to the entire original smaller overlap. -/
def restOverlapRestriction (k : ℕ) (X : SSet.{u}) :
    restBoundaryJoinedPresheaf k X ⟶ boundaryJoinedPresheaf k X where
  app q g := boundaryToRest k q.unop.len ≫ g
  naturality a b β := by
    funext g
    change boundaryToRest k b.unop.len ≫
        (DaggerOriginalRestPrefixBoundaryFunctor.restPrefixBoundaryMap k β.unop ≫ g) =
      DaggerOriginalJoinedPrefixBoundaryFunctor.prefixBoundaryMap k β.unop ≫
        (boundaryToRest k a.unop.len ≫ g)
    rw [← Category.assoc, ← boundaryToRest_naturality, Category.assoc]

/-- Original Yoneda transports the actual pointwise mapping pullback with its exact maps. -/
theorem successorBoundaryRestriction_app_isPullback (k : ℕ) (X : SSet.{u})
    (q : SimplexCategoryᵒᵖ) :
    IsPullback ((successorFirstRestriction k X).app q) ((successorRestRestriction k X).app q)
      ((joinedBoundaryRestriction k X).app q) ((restOverlapRestriction k X).app q) := by
  apply (successor_boundary_maps_isPullback X k q.unop.len).flip.of_iso
    (Iso.refl _) (Equiv.toIso (SSet.yonedaEquiv (X := X)
      (n := ⦋k + q.unop.len + 1⦌))) (Iso.refl _) (Iso.refl _)
  · funext s
    rfl
  · rfl
  · funext s
    change (DaggerOriginalJoinedHornGeometry.prefixBoundary k q.unop.len).ι ≫ s =
      (DaggerOriginalJoinedHornGeometry.prefixBoundary k q.unop.len).ι ≫
        SSet.yonedaEquiv.symm (SSet.yonedaEquiv s)
    rw [Equiv.symm_apply_apply]
  · rfl

/-- The actual restriction square commutes over maps from the entire original overlap. -/
theorem successorBoundaryRestriction_square (k : ℕ) (X : SSet.{u}) :
    successorFirstRestriction k X ≫ joinedBoundaryRestriction k X =
      successorRestRestriction k X ≫ restOverlapRestriction k X := by
  ext q s
  exact congrFun (successorBoundaryRestriction_app_isPullback k X q).w s

/-- The original successor-boundary mapping square is an actual pullback of simplicial sets. -/
theorem successorBoundaryRestriction_isPullback (k : ℕ) (X : SSet.{u}) :
    IsPullback (successorFirstRestriction k X) (successorRestRestriction k X)
      (joinedBoundaryRestriction k X) (restOverlapRestriction k X) := by
  let c := PullbackCone.mk (successorFirstRestriction k X) (successorRestRestriction k X)
    (successorBoundaryRestriction_square k X)
  apply IsPullback.of_isLimit (c := c)
  apply evaluationJointlyReflectsLimits
  intro q
  let h := successorBoundaryRestriction_app_isPullback k X q
  refine IsLimit.equivOfNatIsoOfIso ?_ _ _ ?_ h.isLimit
  · exact cospanIsoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · refine Cones.ext (Iso.refl _) ?_
    rintro (_ | _ | _) <;> rfl

end

end DaggerOriginalSuccessorBoundaryPresheafPullback
