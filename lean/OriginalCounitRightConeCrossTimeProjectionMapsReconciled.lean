import OriginalCounitRightConeCrossTimeSectionsReconciled
import OriginalRigidificationZeroHomReconciled

/-!
# Whole-map coordinate identities for the two cross-time sections

These equations are in simplicial sets, before applying the original
rigidification. The separate zero-simplex Hom calculation is imported for
the next identity-on-a-constant-arrow step.
-/

set_option autoImplicit false

open CategoryTheory CartesianMonoidalCategory Opposite Simplicial
open DaggerOriginalCounitRightConeCrossTimeSections

universe u

namespace DaggerOriginalCounitRightConeCrossTimeProjectionMaps

noncomputable section

variable (X : SSet.{u}) (a : X.obj (op ⦋0⦌))
variable (i : (Δ[1] : SSet.{u}).obj (op ⦋0⦌))

/-- The first projection of either horizontal placement is literally the identity. -/
theorem horizontalAt_fst :
    horizontalAt X i ≫ fst X (Δ[1] : SSet.{u}) = 𝟙 X := by
  exact lift_fst _ _

/-- The second projection of a horizontal placement is its actual constant time. -/
theorem horizontalAt_snd :
    horizontalAt X i ≫ snd X (Δ[1] : SSet.{u}) = SSet.const i := by
  exact lift_snd _ _

/-- The first projection of a vertical line is constant at its chosen vertex. -/
theorem verticalAt_fst :
    verticalAt X a ≫ fst X (Δ[1] : SSet.{u}) = SSet.const a := by
  exact lift_fst _ _

/-- The second projection of a vertical line is the actual identity of `Δ[1]`. -/
theorem verticalAt_snd :
    verticalAt X a ≫ snd X (Δ[1] : SSet.{u}) = 𝟙 (Δ[1] : SSet.{u}) := by
  exact lift_snd _ _

end

end DaggerOriginalCounitRightConeCrossTimeProjectionMaps
