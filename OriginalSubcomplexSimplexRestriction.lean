import OriginalSubcomplexNerveData
import RigidificationCofSimplexRestriction

set_option autoImplicit false

open CategoryTheory Opposite
open scoped Simplicial

universe u

namespace DaggerOrdinaryRigidificationCof.SubcomplexNerveData

open BoundaryData

variable {d : ℕ} (K : (Δ[d] : SSet.{u}).Subcomplex) {A : SC.{u}}

/-- Factor any included ordinal simplex through an actually included finite face. -/
theorem simplex_from_face (a : (K : SSet) ⟶ N.obj A)
    (s : Finset (Fin (d + 1))) (hs : s.Nonempty)
    (hface : Contains K (faceOrdinal s hs))
    {m : SimplexCategory} (φ : m ⟶ ⦋d⦌) (hφ : ∀ i, φ.toOrderHom i ∈ s)
    (hmem : Contains K φ) :
    SimplicialThickening.functor (faceLift s φ hφ).uliftMap ≫
      faceFunctor K a s hs hface = simplex K a φ hmem := by
  have h := (simplex_precompose K a (faceOrdinal s hs) hface
    (factorOrdinal s hs φ hφ)).trans
      (simplex_eq K a (factorOrdinal_comp s hs φ hφ) _ hmem)
  unfold faceFunctor
  rw [← Category.assoc]
  change EnrichedFunctor.comp SSet
    (EnrichedFunctor.comp SSet (SimplicialThickening.functor (faceLift s φ hφ).uliftMap)
      (SimplicialThickening.functor (faceBackward s hs).uliftMap)) _ = _
  rw [← SimplicialThickening.functor_comp]
  exact h

end DaggerOrdinaryRigidificationCof.SubcomplexNerveData
