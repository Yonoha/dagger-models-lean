import OriginalSuccessorBoundaryPresheafPullback
import OriginalCosliceLeftLiftingProperty

/-!
# All nonfinal horn lifts for the original successor-to-rest restriction

The actual successor restriction square is a presheaf pullback. Apply the
native pullback lifting theorem to the proved original joined-boundary
restriction lifting property. Retain every prefix dimension, original horn
inclusion, commuting square and arbitrary universe. No cone inverse is assumed.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerOriginalInnerHornFillers DaggerOriginalJoinedBoundaryRestriction
open DaggerOriginalCosliceLeftLiftingProperty
open DaggerOriginalPrefixBoundaryConeTransposition
open DaggerOriginalSuccessorBoundaryPresheafPullback

universe u

namespace DaggerOriginalSuccessorBoundaryRestLifting

/-- The actual successor-to-rest restriction lifts every original nonfinal horn. -/
theorem successorRestRestriction_hasLiftingProperty {X : SSet.{u}}
    (hX : innerHornFillers X) (k n : ℕ) (i : Fin (n + 2)) (hi : i < Fin.last (n + 1)) :
    HasLiftingProperty (Λ[n + 1, i] : (Δ[n + 1] : SSet.{u}).Subcomplex).ι
      (successorRestRestriction k X) := by
  haveI := joined_hasLiftingProperty hX k n i hi
  exact (successorBoundaryRestriction_isPullback k X).hasLiftingProperty _

/-- Every actual relative horn square has a lift retaining both original restriction equations.
-/
theorem successorRestRestriction_horn_lift {X : SSet.{u}} (hX : innerHornFillers X)
    (k n : ℕ) (i : Fin (n + 2)) (hi : i < Fin.last (n + 1))
    (φ : ((Λ[n + 1, i] : (Δ[n + 1] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶
      boundaryJoinedPresheaf (k + 1) X)
    (β : (Δ[n + 1] : SSet.{u}) ⟶ restBoundaryJoinedPresheaf k X)
    (w : φ ≫ successorRestRestriction k X =
      (Λ[n + 1, i] : (Δ[n + 1] : SSet.{u}).Subcomplex).ι ≫ β) :
    ∃ σ : (Δ[n + 1] : SSet.{u}) ⟶ boundaryJoinedPresheaf (k + 1) X,
      φ = (Λ[n + 1, i] : (Δ[n + 1] : SSet.{u}).Subcomplex).ι ≫ σ ∧
        σ ≫ successorRestRestriction k X = β := by
  haveI := successorRestRestriction_hasLiftingProperty hX k n i hi
  let sq : CommSq φ (Λ[n + 1, i] : (Δ[n + 1] : SSet.{u}).Subcomplex).ι
    (successorRestRestriction k X) β := ⟨w⟩
  haveI := HasLiftingProperty.sq_hasLift sq
  exact ⟨sq.lift, sq.fac_left.symm, sq.fac_right⟩

end DaggerOriginalSuccessorBoundaryRestLifting
