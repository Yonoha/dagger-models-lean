import OriginalJoinedPresheafAssociativity
import OriginalVertexCosliceLeftLifting

/-!
# All prefix dimensions for the exact original joined suffix projection

Induct on the original prefix dimension. Native associativity factors each
successor projection as its actual isomorphism, the vertex projection of the
previous joined presheaf, and the previous projection. Native lifting properties
compose. The same all-dimensional inner-horn condition is obtained for each
original joined presheaf, without a boundary-projection or Kan assumption.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerOriginalInnerHornFillers
open DaggerOriginalSimplexCoslice
open DaggerOriginalJoinedPresheafAssociativity
open DaggerOriginalVertexCosliceLeftLifting

universe u

namespace DaggerOriginalJoinedAllPrefixProjectionLifting

/-- Simultaneously retain all native nonfinal lifts and inner fillers of the original join. -/
theorem joined_projection_and_inner_family {X : SSet.{u}} (hX : innerHornFillers X)
    (k : ℕ) :
    (∀ (n : ℕ) (i : Fin (n + 2)), i < Fin.last (n + 1) →
      HasLiftingProperty (Λ[n + 1, i] : (Δ[n + 1] : SSet.{u}).Subcomplex).ι
        (suffixProjection ⦋k⦌ X)) ∧ innerHornFillers (joinedPresheaf ⦋k⦌ X) := by
  induction k with
  | zero =>
    have hl := fun n i hi ↦ joined_vertex_projection_hasLiftingProperty hX n i hi
    exact ⟨hl, innerHornFillers_of_nonfinal_lifting (suffixProjection ⦋0⦌ X) hX hl⟩
  | succ k ih =>
    have hl : ∀ (n : ℕ) (i : Fin (n + 2)), i < Fin.last (n + 1) →
        HasLiftingProperty (Λ[n + 1, i] : (Δ[n + 1] : SSet.{u}).Subcomplex).ι
          (suffixProjection ⦋k + 1⦌ X) := by
      intro n i hi
      haveI := ih.1 n i hi
      haveI := joined_vertex_projection_hasLiftingProperty ih.2 n i hi
      have hk : AugmentedSimplexCategory.tensorObjOf ⦋k⦌ ⦋0⦌ = ⦋k + 1⦌ := by
        simp only [AugmentedSimplexCategory.tensorObjOf, SimplexCategory.len_mk, Nat.add_zero]
      rw [← hk, ← joinedAssociativityIso_comp_projections ⦋k⦌ ⦋0⦌ X]
      infer_instance
    exact ⟨hl, innerHornFillers_of_nonfinal_lifting (suffixProjection ⦋k + 1⦌ X) hX hl⟩

/-- The exact original joined suffix projection lifts every nonfinal horn in every prefix
and horn dimension. -/
theorem joined_projection_hasLiftingProperty {X : SSet.{u}} (hX : innerHornFillers X)
    (k n : ℕ) (i : Fin (n + 2)) (hi : i < Fin.last (n + 1)) :
    HasLiftingProperty (Λ[n + 1, i] : (Δ[n + 1] : SSet.{u}).Subcomplex).ι
      (suffixProjection ⦋k⦌ X) := (joined_projection_and_inner_family hX k).1 n i hi

/-- The actual joined presheaf has original inner-horn fillers in every prefix dimension. -/
theorem joined_innerHornFillers {X : SSet.{u}} (hX : innerHornFillers X) (k : ℕ) :
    innerHornFillers (joinedPresheaf ⦋k⦌ X) := (joined_projection_and_inner_family hX k).2

end DaggerOriginalJoinedAllPrefixProjectionLifting
