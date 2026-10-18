import OriginalZeroBoundaryProjectionIso

/-!
# Native left-horn lifting for the original vertex coslice projection

Factor the same original suffix projection through the proved boundary
restriction and the exact zero-prefix boundary isomorphism. Native lifting
properties compose. Since the target has the original inner-horn fillers,
the actual vertex coslice itself has those same fillers in arbitrary universe.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerOriginalInnerHornFillers
open DaggerOriginalSimplexCoslice
open DaggerOriginalJoinedBoundaryRestriction
open DaggerOriginalJoinedBoundaryProjection
open DaggerOriginalCosliceLeftLiftingProperty
open DaggerOriginalZeroBoundaryProjectionIso

universe u

namespace DaggerOriginalVertexCosliceLeftLifting

/-- The original joined vertex projection lifts every original nonfinal horn. -/
theorem joined_vertex_projection_hasLiftingProperty {X : SSet.{u}} (hX : innerHornFillers X)
    (n : ℕ) (i : Fin (n + 2)) (hi : i < Fin.last (n + 1)) :
    HasLiftingProperty (Λ[n + 1, i] : (Δ[n + 1] : SSet.{u}).Subcomplex).ι
      (suffixProjection ⦋0⦌ X) := by
  rw [← joinedBoundaryRestriction_comp_projection 0 X]
  haveI := joined_hasLiftingProperty hX 0 n i hi
  haveI := boundaryProjection_zero_hasLiftingProperty X
    (Λ[n + 1, i] : (Δ[n + 1] : SSet.{u}).Subcomplex).ι
  infer_instance

/-- The exact original vertex coslice projection lifts every original nonfinal horn. -/
theorem vertex_coslice_projection_hasLiftingProperty {X : SSet.{u}} (hX : innerHornFillers X)
    (n : ℕ) (i : Fin (n + 2)) (hi : i < Fin.last (n + 1)) (f : X.obj (op ⦋0⦌)) :
    HasLiftingProperty (Λ[n + 1, i] : (Δ[n + 1] : SSet.{u}).Subcomplex).ι
      (cosliceProjection ⦋0⦌ X f) := by
  rw [← cosliceBoundaryRestriction_comp_projection 0 X f]
  haveI := coslice_hasLiftingProperty hX 0 n i hi f
  haveI := boundaryProjection_zero_hasLiftingProperty X
    (Λ[n + 1, i] : (Δ[n + 1] : SSet.{u}).Subcomplex).ι
  infer_instance

/-- Original nonfinal lifting plus original target inner filling gives original source inner
filling. -/
theorem innerHornFillers_of_nonfinal_lifting {E X : SSet.{u}} (p : E ⟶ X)
    (hX : innerHornFillers X)
    (hleft : ∀ (n : ℕ) (i : Fin (n + 2)), i < Fin.last (n + 1) →
      HasLiftingProperty (Λ[n + 1, i] : (Δ[n + 1] : SSet.{u}).Subcomplex).ι p) :
    innerHornFillers E := by
  intro n i h0 hi φ
  cases n with
  | zero =>
    have hj := i.isLt
    change 0 < i.val at h0
    exact False.elim (by omega)
  | succ n =>
    haveI := hleft n i hi
    obtain ⟨β, w⟩ := hX h0 hi (φ ≫ p)
    let sq : CommSq φ (Λ[n + 1, i] : (Δ[n + 1] : SSet.{u}).Subcomplex).ι p β := ⟨w⟩
    haveI : sq.HasLift := HasLiftingProperty.sq_hasLift sq
    exact ⟨sq.lift, sq.fac_left.symm⟩

/-- The actual original vertex coslice is an inner-horn input in every universe. -/
theorem vertex_coslice_innerHornFillers {X : SSet.{u}} (hX : innerHornFillers X)
    (f : X.obj (op ⦋0⦌)) : innerHornFillers (simplexCoslice ⦋0⦌ X f) :=
  innerHornFillers_of_nonfinal_lifting (cosliceProjection ⦋0⦌ X f) hX
    (fun n i hi ↦ vertex_coslice_projection_hasLiftingProperty hX n i hi f)

end DaggerOriginalVertexCosliceLeftLifting
