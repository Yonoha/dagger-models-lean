import Mathlib.AlgebraicTopology.SimplicialSet.Op
import Mathlib.AlgebraicTopology.SimplicialSet.Horn

/-!
# Native standard simplices under the original simplicial reversal

Reversing the actual simplex operator gives a natural isomorphism from the
native opposite standard simplex to the same native standard simplex. Its
inverse retains the same original operator. The construction uses the native
reversal functor and native standard-simplex equivalence in arbitrary universe.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial

universe u

namespace DaggerOriginalStandardSimplexReversal

noncomputable section

/-- Native reversal applied twice keeps the exact original simplex operator. -/
theorem reverse_operator_twice {m n : SimplexCategory} (α : m ⟶ n) :
    SimplexCategory.rev.map (SimplexCategory.rev.map α) = α := by
  ext i : 3
  simp only [SimplexCategory.rev_map_apply, Fin.rev_rev]

/-- The original opposite standard simplex maps to itself by native operator reversal. -/
def standardSimplexReversalHom (n : ℕ) : (Δ[n] : SSet.{u}).op ⟶ Δ[n] where
  app q s := SSet.stdSimplex.objEquiv.symm
    (SimplexCategory.rev.map (SSet.stdSimplex.objEquiv (SSet.opObjEquiv s)))
  naturality a b f := by
    funext s
    apply SSet.stdSimplex.objEquiv.injective
    change SimplexCategory.rev.map (SimplexCategory.rev.map f.unop ≫
      SSet.stdSimplex.objEquiv (SSet.opObjEquiv s)) =
        f.unop ≫ SimplexCategory.rev.map (SSet.stdSimplex.objEquiv (SSet.opObjEquiv s))
    rw [Functor.map_comp, reverse_operator_twice]
    rfl

/-- The inverse keeps the original native opposite and reverses the same simplex operator. -/
def standardSimplexReversalInv (n : ℕ) : (Δ[n] : SSet.{u}) ⟶ (Δ[n] : SSet.{u}).op where
  app q s := SSet.opObjEquiv.symm (SSet.stdSimplex.objEquiv.symm
    (SimplexCategory.rev.map (SSet.stdSimplex.objEquiv s)))
  naturality a b f := by
    funext s
    apply SSet.opObjEquiv.injective
    apply SSet.stdSimplex.objEquiv.injective
    change SimplexCategory.rev.map (f.unop ≫ SSet.stdSimplex.objEquiv s) =
      SimplexCategory.rev.map f.unop ≫ SimplexCategory.rev.map (SSet.stdSimplex.objEquiv s)
    exact Functor.map_comp _ _ _

/-- The original standard simplex and its native opposite are naturally isomorphic. -/
def standardSimplexReversalIso (n : ℕ) : (Δ[n] : SSet.{u}).op ≅ Δ[n] where
  hom := standardSimplexReversalHom n
  inv := standardSimplexReversalInv n
  hom_inv_id := by
    ext q s
    apply SSet.opObjEquiv.injective
    apply SSet.stdSimplex.objEquiv.injective
    change SimplexCategory.rev.map (SimplexCategory.rev.map
      (SSet.stdSimplex.objEquiv (SSet.opObjEquiv s))) =
        SSet.stdSimplex.objEquiv (SSet.opObjEquiv s)
    exact reverse_operator_twice _
  inv_hom_id := by
    ext q s
    apply SSet.stdSimplex.objEquiv.injective
    change SimplexCategory.rev.map (SimplexCategory.rev.map
      (SSet.stdSimplex.objEquiv s)) = SSet.stdSimplex.objEquiv s
    exact reverse_operator_twice _

end

end DaggerOriginalStandardSimplexReversal
