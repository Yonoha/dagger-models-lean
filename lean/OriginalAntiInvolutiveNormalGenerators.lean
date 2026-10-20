import OriginalAntiInvolutiveNormalOrbits
import OriginalAntiInvolutiveFreePairMono
import Mathlib.AlgebraicTopology.SimplicialSet.Boundary

/-!
# Literal free boundary arrows in anti-involutive simplicial sets

This file records the actual `freeAnti` boundary generators. Their
point-set analysis requires the explicit two-copy left Kan extension model.
-/

set_option autoImplicit false

open CategoryTheory Simplicial Opposite

universe u

namespace DaggerModels.OriginalAntiInvolutiveNormalGenerators

open DaggerModels.OriginalTaggedReverseFreeCompletion

/-- The literal DCH free boundary generator, with the original `freeAnti`. -/
noncomputable def freeBoundary (n : ℕ) :
    freeAnti.{u}.obj (SSet.boundary n : SSet.{u}) ⟶
      freeAnti.obj (Δ[n] : SSet.{u}) :=
  freeAnti.map (SSet.boundary n).ι

/-- The actual free boundary arrow is monic, including dimension zero. -/
theorem freeBoundary_mono (n : ℕ) : Mono (freeBoundary.{u} n) := by
  unfold freeBoundary
  exact OriginalAntiInvolutiveFreePairMono.freeAnti_map_mono (SSet.boundary n).ι

/-- The literal free boundary generator is normal in every degree. -/
theorem freeBoundary_normal (n : ℕ) :
    AntiInvolutiveSSet.NormalMono (freeBoundary.{u} n) := by
  unfold freeBoundary
  exact OriginalAntiInvolutiveFreePairMono.freeAnti_map_normal (SSet.boundary n).ι

end DaggerModels.OriginalAntiInvolutiveNormalGenerators
