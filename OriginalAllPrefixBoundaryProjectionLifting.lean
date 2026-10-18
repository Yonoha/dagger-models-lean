import OriginalRestBoundaryConeIsomorphism
import OriginalZeroBoundaryProjectionIso
import OriginalJoinedAllPrefixProjectionLifting

/-!
# All original prefix dimensions for whole-boundary projection lifting

The exact zero-prefix projection is an isomorphism. For the successor prefix,
the proved original factorization uses the successor-to-rest restriction,
the actual cone isomorphism, the smaller whole-boundary projection of J_0 X,
and the original vertex projection. Their native lifting properties compose.
Every original nonfinal horn and arbitrary universe is retained; no full Kan
hypothesis or higher-prefix boundary lifting premise is assumed.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerOriginalInnerHornFillers DaggerOriginalSimplexCoslice
open DaggerOriginalJoinedBoundaryRestriction DaggerOriginalJoinedBoundaryProjection
open DaggerOriginalPrefixBoundaryConeTransposition
open DaggerOriginalZeroBoundaryProjectionIso
open DaggerOriginalJoinedAllPrefixProjectionLifting DaggerOriginalVertexCosliceLeftLifting
open DaggerOriginalSuccessorBoundaryRestLifting
open DaggerOriginalSuccessorBoundaryProjectionFactorization
open DaggerOriginalRestBoundaryConeIsomorphism

universe u

namespace DaggerOriginalAllPrefixBoundaryProjectionLifting

/-- The original whole-boundary projection lifts every nonfinal horn in every prefix dimension.
-/
theorem boundaryProjection_hasLiftingProperty {X : SSet.{u}} (hX : innerHornFillers X)
    (k n : ℕ) (i : Fin (n + 2)) (hi : i < Fin.last (n + 1)) :
    HasLiftingProperty (Λ[n + 1, i] : (Δ[n + 1] : SSet.{u}).Subcomplex).ι
      (boundaryProjection k X) := by
  induction k generalizing X with
  | zero => exact boundaryProjection_zero_hasLiftingProperty X _
  | succ k ih =>
    haveI := successorRestRestriction_hasLiftingProperty hX k n i hi
    haveI := restConeTransposition_isIso k X
    haveI := ih (joined_innerHornFillers hX 0)
    haveI := joined_projection_hasLiftingProperty hX 0 n i hi
    rw [← successorBoundaryProjection_factorization k X]
    infer_instance

/-- The actual original whole-boundary mapping presheaf has inner fillers in every prefix
and original horn dimension. -/
theorem boundaryJoinedPresheaf_innerHornFillers {X : SSet.{u}} (hX : innerHornFillers X)
    (k : ℕ) : innerHornFillers (boundaryJoinedPresheaf k X) :=
  innerHornFillers_of_nonfinal_lifting (boundaryProjection k X) hX
    (fun n i hi ↦ boundaryProjection_hasLiftingProperty hX k n i hi)

/-- Every actual original relative horn square for whole-boundary projection has a lift with
both exact original equations, in all positive horn and prefix dimensions. -/
theorem boundaryProjection_horn_lift {X : SSet.{u}} (hX : innerHornFillers X)
    (k n : ℕ) (i : Fin (n + 2)) (hi : i < Fin.last (n + 1))
    (φ : ((Λ[n + 1, i] : (Δ[n + 1] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶
      boundaryJoinedPresheaf k X) (β : (Δ[n + 1] : SSet.{u}) ⟶ X)
    (w : φ ≫ boundaryProjection k X =
      (Λ[n + 1, i] : (Δ[n + 1] : SSet.{u}).Subcomplex).ι ≫ β) :
    ∃ σ : (Δ[n + 1] : SSet.{u}) ⟶ boundaryJoinedPresheaf k X,
      φ = (Λ[n + 1, i] : (Δ[n + 1] : SSet.{u}).Subcomplex).ι ≫ σ ∧
        σ ≫ boundaryProjection k X = β := by
  haveI := boundaryProjection_hasLiftingProperty hX k n i hi
  let sq : CommSq φ (Λ[n + 1, i] : (Δ[n + 1] : SSet.{u}).Subcomplex).ι
    (boundaryProjection k X) β := ⟨w⟩
  haveI := HasLiftingProperty.sq_hasLift sq
  exact ⟨sq.lift, sq.fac_left.symm, sq.fac_right⟩

end DaggerOriginalAllPrefixBoundaryProjectionLifting
