import OriginalJoinedPrefixBoundaryFunctor

/-!
# Actual restriction from joined simplices to joined prefix boundaries

Use the native Yoneda presheaf of maps from each original joined boundary
shape into X. Restriction of an original joined simplex is precomposition
with the same original boundary inclusion. The naturality square uses the
proved inclusion diagram and exact Yoneda operator evaluation. This defines
the actual relative map used in the coslice lifting route, not a fibration
assumption or a replacement for the remaining general outer-horn proof.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerOriginalOrdinalJoinLeft
open DaggerOriginalSimplexCoslice
open DaggerOriginalJoinedHornGeometry
open DaggerOriginalJoinedHornPrefix
open DaggerOriginalJoinedPrefixBoundaryFunctor

universe u

namespace DaggerOriginalJoinedBoundaryRestriction

noncomputable section

/-- The actual presheaf of maps from the original joined prefix-boundary shapes into X. -/
def boundaryJoinedPresheaf (k : ℕ) (X : SSet.{u}) : SSet.{u} :=
  (prefixBoundaryFunctor k).op ⋙ CategoryTheory.yoneda.obj X

/-- Restrict every original joined simplex to the same joined prefix boundary. -/
def joinedBoundaryRestriction (k : ℕ) (X : SSet.{u}) :
    joinedPresheaf ⦋k⦌ X ⟶ boundaryJoinedPresheaf k X where
  app n s := (prefixBoundary k n.unop.len).ι ≫
    (SSet.yonedaEquiv (X := X) (n := ⦋k + n.unop.len + 1⦌)).symm s
  naturality a b φ := by
    funext s
    let β : ⦋k + b.unop.len + 1⦌ ⟶ ⦋k + a.unop.len + 1⦌ :=
      (ordinalJoinLeft ⦋k⦌).map φ.unop
    have hμ : (SSet.yonedaEquiv (X := X) (n := ⦋k + b.unop.len + 1⦌)).symm
        (X.map β.op s) = SSet.stdSimplex.map β ≫
        (SSet.yonedaEquiv (X := X) (n := ⦋k + a.unop.len + 1⦌)).symm s := by
      apply SSet.yonedaEquiv.injective
      rw [Equiv.apply_symm_apply, yonedaEquiv_precomp_operator, Equiv.apply_symm_apply]
    change (prefixBoundary k b.unop.len).ι ≫
      (SSet.yonedaEquiv (X := X) (n := ⦋k + b.unop.len + 1⦌)).symm (X.map β.op s) =
      prefixBoundaryMap k φ.unop ≫ ((prefixBoundary k a.unop.len).ι ≫
        (SSet.yonedaEquiv (X := X) (n := ⦋k + a.unop.len + 1⦌)).symm s)
    rw [hμ, ← Category.assoc, ← Category.assoc, prefixBoundaryMap_comp_inclusion]

/-- In every degree this is exactly the original boundary inclusion and original simplex. -/
theorem joinedBoundaryRestriction_app (k : ℕ) (X : SSet.{u})
    (n : SimplexCategoryᵒᵖ) (s : (joinedPresheaf ⦋k⦌ X).obj n) :
    (joinedBoundaryRestriction k X).app n s = (prefixBoundary k n.unop.len).ι ≫
      (SSet.yonedaEquiv (X := X) (n := ⦋k + n.unop.len + 1⦌)).symm s := rfl

/-- The same boundary restriction on actual fixed-prefix coslice simplices. -/
def cosliceBoundaryRestriction (k : ℕ) (X : SSet.{u}) (f : X.obj (op ⦋k⦌)) :
    simplexCoslice ⦋k⦌ X f ⟶ boundaryJoinedPresheaf k X :=
  (prefixFiber ⦋k⦌ X f).ι ≫ joinedBoundaryRestriction k X

/-- Its degreewise map retains the original coslice simplex before boundary restriction. -/
theorem cosliceBoundaryRestriction_app (k : ℕ) (X : SSet.{u}) (f : X.obj (op ⦋k⦌))
    (n : SimplexCategoryᵒᵖ) (s : (simplexCoslice ⦋k⦌ X f).obj n) :
    (cosliceBoundaryRestriction k X f).app n s = (prefixBoundary k n.unop.len).ι ≫
      (SSet.yonedaEquiv (X := X) (n := ⦋k + n.unop.len + 1⦌)).symm s.val := rfl

end

end DaggerOriginalJoinedBoundaryRestriction
