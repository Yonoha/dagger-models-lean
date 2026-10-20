import Mathlib.Combinatorics.Quiver.ReflQuiver
import ActualAntiInvolutiveLimits
import OriginalAntiInvolutiveNormalGeneratorRecognition
import Mathlib.CategoryTheory.SmallObject.Basic

/-!
# Normal right lifting is exactly underlying ordinary boundary lifting

Reuse the full original all-degree normal generator saturation theorem and
the original freeAnti adjunction. Both directions concern the entire original maps.
No DCH or ordinary Joyal model structure is assumed.
-/
set_option autoImplicit false
open CategoryTheory Limits DaggerModels
open DaggerModels.OriginalTaggedReverseFreeCompletion
open DaggerModels.OriginalAntiInvolutiveNormalMonoSaturation
open DaggerModels.OriginalAntiInvolutiveNormalGeneratorRecognition
universe u
namespace DaggerActualAntiNormalBoundaryLifting

/-- The original full normal class lies in the left lifting class of its original generators. -/
theorem normalMonos_le_generator_rlp_llp :
    normalMonos.{u} ≤ normalGeneratingCofibrations.{u}.rlp.llp := by
  rw [normalMonos_eq_normalGeneratorSaturation]
  exact MorphismProperty.retracts_transfiniteComposition_pushouts_coproducts_le_llp_rlp _

/-- The actual normal class and its literal free-boundary generators have identical RLP. -/
theorem normalMonos_rlp_eq_generators_rlp :
    normalMonos.{u}.rlp = normalGeneratingCofibrations.{u}.rlp := by
  apply le_antisymm
  · exact MorphismProperty.antitone_rlp normalGeneratingCofibrations_le_normalMonos
  · calc
      normalGeneratingCofibrations.rlp = normalGeneratingCofibrations.rlp.llp.rlp :=
        (MorphismProperty.rlp_llp_rlp _).symm
      _ ≤ normalMonos.rlp := MorphismProperty.antitone_rlp normalMonos_le_generator_rlp_llp

/-- All normal lifting tests are equivalent to all ordinary boundary tests on the underlying map. -/
theorem normal_rlp_iff_underlying_boundary {X Y : AntiInvolutiveSSet.{u}} (p : X ⟶ Y) :
    normalMonos.rlp p ↔
      ∀ n : ℕ, HasLiftingProperty (SSet.boundary.{u} n).ι p.hom := by
  rw [normalMonos_rlp_eq_generators_rlp]
  constructor
  · intro h n
    exact (freeAntiAdjunction.hasLiftingProperty_iff (SSet.boundary n).ι p).1
      (h _ ⟨n⟩)
  · intro h A B i hi
    obtain ⟨n⟩ := hi
    exact (freeAntiAdjunction.hasLiftingProperty_iff (SSet.boundary n).ι p).2 (h n)

end DaggerActualAntiNormalBoundaryLifting
