import OriginalJoinedBoundarySuffixInclusion

/-!
# The actual boundary-map presheaf projects to the original simplicial set

Evaluate a map from the actual joined prefix boundary on the original right
block. The native block naturality gives every simplex-operator square. The
original joined and fixed-prefix coslice projections factor through this exact
boundary projection, retaining the original suffix map on every simplex.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerOriginalSimplexCoslice
open DaggerOriginalJoinedHornGeometry
open DaggerOriginalJoinedHornPrefix
open DaggerOriginalJoinedPrefixBoundaryFunctor
open DaggerOriginalJoinedBoundaryRestriction
open DaggerOriginalJoinedBoundarySuffixInclusion

universe u

namespace DaggerOriginalJoinedBoundaryProjection

noncomputable section

/-- Evaluate the original boundary simplex on its actual original right block. -/
def boundaryProjection (k : ℕ) (X : SSet.{u}) : boundaryJoinedPresheaf k X ⟶ X where
  app n g := SSet.yonedaEquiv (boundarySuffixInclusion k n.unop ≫ g)
  naturality a b φ := by
    induction a using Opposite.rec with | op a =>
      induction a using SimplexCategory.rec with | h a =>
        induction b using Opposite.rec with | op b =>
          induction b using SimplexCategory.rec with | h b =>
            funext g
            change SSet.yonedaEquiv (boundarySuffixInclusion k ⦋b⦌ ≫
              (prefixBoundaryMap k φ.unop ≫ g)) =
              X.map φ (SSet.yonedaEquiv (boundarySuffixInclusion k ⦋a⦌ ≫ g))
            rw [← Category.assoc, boundarySuffixInclusion_naturality, Category.assoc]
            exact yonedaEquiv_precomp_operator (boundarySuffixInclusion k ⦋a⦌ ≫ g) φ.unop

/-- In every degree the projection is evaluation on the same original suffix inclusion. -/
theorem boundaryProjection_app (k : ℕ) (X : SSet.{u})
    (n : SimplexCategoryᵒᵖ) (g : (boundaryJoinedPresheaf k X).obj n) :
    (boundaryProjection k X).app n g =
      SSet.yonedaEquiv (boundarySuffixInclusion k n.unop ≫ g) := rfl

/-- The original joined projection is restriction to the boundary followed by this projection. -/
theorem joinedBoundaryRestriction_comp_projection (k : ℕ) (X : SSet.{u}) :
    joinedBoundaryRestriction k X ≫ boundaryProjection k X = suffixProjection ⦋k⦌ X := by
  ext n s
  induction n using Opposite.rec with | op n =>
    induction n using SimplexCategory.rec with | h n =>
      change SSet.yonedaEquiv (boundarySuffixInclusion k ⦋n⦌ ≫
        ((prefixBoundary k n).ι ≫
          (SSet.yonedaEquiv (X := X) (n := ⦋k + n + 1⦌)).symm s)) =
        X.map (AugmentedSimplexCategory.inr' ⦋k⦌ ⦋n⦌).op s
      have hinc := boundarySuffixInclusion_comp.{u} k ⦋n⦌
      change boundarySuffixInclusion k ⦋n⦌ ≫ (prefixBoundary k n).ι =
        SSet.stdSimplex.map (AugmentedSimplexCategory.inr' ⦋k⦌ ⦋n⦌) at hinc
      rw [← Category.assoc, hinc]
      have h := yonedaEquiv_precomp_operator (k := n) (m := k + n + 1)
        ((SSet.yonedaEquiv (X := X) (n := ⦋k + n + 1⦌)).symm s)
          (AugmentedSimplexCategory.inr' ⦋k⦌ ⦋n⦌)
      rw [Equiv.apply_symm_apply] at h
      exact h

/-- The same factorization holds for the original coslice with its exact original prefix. -/
theorem cosliceBoundaryRestriction_comp_projection (k : ℕ) (X : SSet.{u})
    (f : X.obj (op ⦋k⦌)) :
    cosliceBoundaryRestriction k X f ≫ boundaryProjection k X = cosliceProjection ⦋k⦌ X f := by
  change ((prefixFiber ⦋k⦌ X f).ι ≫ joinedBoundaryRestriction k X) ≫
    boundaryProjection k X = (prefixFiber ⦋k⦌ X f).ι ≫ suffixProjection ⦋k⦌ X
  rw [Category.assoc, joinedBoundaryRestriction_comp_projection]

end

end DaggerOriginalJoinedBoundaryProjection
