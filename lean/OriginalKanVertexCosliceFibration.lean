import OriginalCosliceKanHornLifting
import OriginalZeroBoundaryProjectionIso
import OriginalNativeKanFromHornFillers
import TopCatModelCategory.ModelCategorySSet

/-!
# The actual vertex coslice projection is a Kan fibration

All original fixed-prefix lifting squares now fill for a Kan input, including
the final missing face. The existing zero-prefix boundary projection isomorphism
therefore gives all horn lifting for the exact original suffix projection.
Native fibration recognition and the same lifting squares give its source Kan
condition, in arbitrary universe.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial HomotopicalAlgebra
open SSet.modelCategoryQuillen
open DaggerOriginalSimplexCoslice DaggerOriginalJoinedBoundaryRestriction
open DaggerOriginalJoinedBoundaryProjection DaggerOriginalCosliceKanHornLifting
open DaggerOriginalZeroBoundaryProjectionIso DaggerOriginalNativeKanFromHornFillers

universe u

namespace DaggerOriginalKanVertexCosliceFibration

noncomputable section

/-- The exact fixed-prefix boundary restriction has native lifting for every original horn. -/
theorem coslice_kan_hasLiftingProperty {X : SSet.{u}} [X.KanComplex]
    (k n : ℕ) (i : Fin (n + 2)) (x : X.obj (op ⦋k⦌)) :
    HasLiftingProperty (Λ[n + 1, i] : (Δ[n + 1] : SSet.{u}).Subcomplex).ι
      (cosliceBoundaryRestriction k X x) where
  sq_hasLift := by
    intro φ β sq
    obtain ⟨σ, hσhorn, hσboundary⟩ :=
      cosliceBoundaryRestriction_kan_horn_lift k n i x φ β sq.w
    exact CommSq.HasLift.mk' ⟨σ, hσhorn.symm, hσboundary⟩

/-- The exact original vertex-coslice suffix projection lifts every original horn. -/
theorem vertex_coslice_projection_hasLiftingProperty_kan {X : SSet.{u}} [X.KanComplex]
    (n : ℕ) (i : Fin (n + 2)) (x : X.obj (op ⦋0⦌)) :
    HasLiftingProperty (Λ[n + 1, i] : (Δ[n + 1] : SSet.{u}).Subcomplex).ι
      (cosliceProjection ⦋0⦌ X x) := by
  rw [← cosliceBoundaryRestriction_comp_projection 0 X x]
  haveI := coslice_kan_hasLiftingProperty 0 n i x
  haveI := boundaryProjection_zero_hasLiftingProperty X
    (Λ[n + 1, i] : (Δ[n + 1] : SSet.{u}).Subcomplex).ι
  infer_instance

/-- The same original suffix projection is a native Kan-model fibration. -/
theorem vertex_coslice_projection_fibration (X : SSet.{u}) [X.KanComplex]
    (x : X.obj (op ⦋0⦌)) : Fibration (cosliceProjection ⦋0⦌ X x) := by
  rw [fibration_iff]
  intro P Q f hf
  simp only [J, MorphismProperty.iSup_iff] at hf
  obtain ⟨n, ⟨i⟩⟩ := hf
  exact vertex_coslice_projection_hasLiftingProperty_kan n i x

/-- The original vertex coslice itself is Kan for a Kan input. -/
theorem vertex_coslice_kan (X : SSet.{u}) [X.KanComplex] (x : X.obj (op ⦋0⦌)) :
    (simplexCoslice ⦋0⦌ X x).KanComplex := by
  apply kanComplex_of_hornFillers
  intro n i φ
  haveI := vertex_coslice_projection_hasLiftingProperty_kan n i x
  obtain ⟨β, w⟩ := SSet.KanComplex.hornFilling (φ ≫ cosliceProjection ⦋0⦌ X x)
  let sq : CommSq φ (Λ[n + 1, i] : (Δ[n + 1] : SSet.{u}).Subcomplex).ι
      (cosliceProjection ⦋0⦌ X x) β := ⟨w⟩
  haveI : sq.HasLift := HasLiftingProperty.sq_hasLift sq
  exact ⟨sq.lift, sq.fac_left.symm⟩

end

end DaggerOriginalKanVertexCosliceFibration
