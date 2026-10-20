import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
import Mathlib.AlgebraicTopology.SimplexCategory.Rev

/-!
# Reversal of standard simplices and their literal boundaries

The true tag of a free anti-involutive cell has reversed simplex operators.
This equivalence reindexes those parameters, including in degree zero, and
preserves membership in the standard boundary.
-/

set_option autoImplicit false

open CategoryTheory Simplicial Opposite

universe u

namespace DaggerModels.OriginalAntiInvolutiveSimplexReversal

/-- Reversing both ordered vertex sets is an involution on simplex operators. -/
def homRevEquiv (m n : SimplexCategory) : (m ⟶ n) ≃ (m ⟶ n) where
  toFun := SimplexCategory.rev.map
  invFun := SimplexCategory.rev.map
  left_inv α := SimplexCategory.rev_map_rev_map α
  right_inv α := SimplexCategory.rev_map_rev_map α

/-- An actual simplex parameter and its reversed parameter. -/
def simplexRevEquiv (n : ℕ) (k : SimplexCategoryᵒᵖ) :
    (Δ[n] : SSet.{u}).obj k ≃ (Δ[n] : SSet.{u}).obj k :=
  (SSet.stdSimplex.objEquiv).trans
    ((homRevEquiv k.unop ⦋n⦌).trans SSet.stdSimplex.objEquiv.symm)

/-- Reversal preserves surjectivity of a simplex-category operator. -/
theorem rev_surjective_iff {m n : SimplexCategory} (α : m ⟶ n) :
    Function.Surjective (SimplexCategory.rev.map α).toOrderHom ↔
      Function.Surjective α.toOrderHom := by
  constructor
  · intro h y
    obtain ⟨x, hx⟩ := h y.rev
    refine ⟨x.rev, ?_⟩
    have h' := congrArg Fin.rev hx
    simpa [SimplexCategory.rev_map_apply] using h'
  · intro h y
    obtain ⟨x, hx⟩ := h y.rev
    refine ⟨x.rev, ?_⟩
    simp [SimplexCategory.rev_map_apply, hx]

/-- The reversed parameter is in the literal boundary exactly when the
original parameter is. -/
theorem simplexRev_mem_boundary_iff (n : ℕ) (k : SimplexCategoryᵒᵖ)
    (a : (Δ[n] : SSet.{u}).obj k) :
    simplexRevEquiv n k a ∈ (SSet.boundary.{u} n).obj k ↔
      a ∈ (SSet.boundary.{u} n).obj k := by
  change ¬ Function.Surjective
      (SSet.stdSimplex.objEquiv (simplexRevEquiv n k a)).toOrderHom ↔
    ¬ Function.Surjective (SSet.stdSimplex.objEquiv a).toOrderHom
  exact not_congr (rev_surjective_iff (SSet.stdSimplex.objEquiv a))

end DaggerModels.OriginalAntiInvolutiveSimplexReversal
