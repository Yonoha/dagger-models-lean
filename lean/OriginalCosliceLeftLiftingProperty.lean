import OriginalCosliceLeftHornLifting
import Mathlib.CategoryTheory.LiftingProperties.Basic

/-!
# Native lifting-property certificates for original coslice restrictions

Connect the constructed original relative lifts to Mathlib's existing
HasLiftingProperty and CommSq.LiftStruct API. The certificates quantify over
all commuting squares for each original nonfinal horn inclusion, in every
positive dimension, arbitrary prefix dimension and arbitrary universe.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerOriginalInnerHornFillers
open DaggerOriginalJoinedBoundaryRestriction
open DaggerOriginalJoinedLeftHornLifting
open DaggerOriginalCosliceLeftHornLifting

universe u

namespace DaggerOriginalCosliceLeftLiftingProperty

/-- The original joined restriction has Mathlib's lifting property for every nonfinal horn. -/
theorem joined_hasLiftingProperty {X : SSet.{u}} (hX : innerHornFillers X)
    (k n : ℕ) (i : Fin (n + 2)) (hi : i < Fin.last (n + 1)) :
    HasLiftingProperty (Λ[n + 1, i] : (Δ[n + 1] : SSet.{u}).Subcomplex).ι
      (joinedBoundaryRestriction k X) where
  sq_hasLift := by
    intro φ β sq
    obtain ⟨σ, hσhorn, hσboundary⟩ :=
      joinedBoundaryRestriction_left_horn_lift hX k n i hi φ β sq.w
    exact CommSq.HasLift.mk' ⟨σ, hσhorn.symm, hσboundary⟩

/-- The same native lifting property holds for the actual original fixed-prefix coslice. -/
theorem coslice_hasLiftingProperty {X : SSet.{u}} (hX : innerHornFillers X)
    (k n : ℕ) (i : Fin (n + 2)) (hi : i < Fin.last (n + 1)) (f : X.obj (op ⦋k⦌)) :
    HasLiftingProperty (Λ[n + 1, i] : (Δ[n + 1] : SSet.{u}).Subcomplex).ι
      (cosliceBoundaryRestriction k X f) where
  sq_hasLift := by
    intro φ β sq
    obtain ⟨σ, hσhorn, hσboundary⟩ :=
      cosliceBoundaryRestriction_left_horn_lift hX k n i hi f φ β sq.w
    exact CommSq.HasLift.mk' ⟨σ, hσhorn.symm, hσboundary⟩

end DaggerOriginalCosliceLeftLiftingProperty
