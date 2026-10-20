import ActualAntiJoyalMappingWeakProperties
import ActualTaggedWalkingJoyalMappingWeak
import ActualTaggedObstructionsForStandardDaggerModel

/-!
# An unconditional original walking obstruction for the exact requested classes

The literal generator is normal and underlying Joyal weak, but its literal left
Kan image is not weak in the constructed standard dagger model. This establishes
the class obstruction without assuming an anti-involutive model. Constructing the
full DCH model and proving its class identities are separate remaining tasks.
-/
set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra DaggerModels
open DaggerModels.OriginalTaggedReverseAdjunctions
open DaggerActualTaggedWalkingIsoImageDKObstruction
open DaggerActualTaggedWalkingIsoSourceHomotopy
open DaggerActualTaggedObstructionsForStandardDaggerModel
universe u
namespace DaggerActualTaggedJoyalClassObstruction
noncomputable section

local instance : ModelCategory DaggerSSet.{u} := DaggerActualRigidificationQuillen.modelD.{u}

/-- The unchanged normal-monomorphism class on the original anti-involutive category. -/
def normalCofibrations : MorphismProperty AntiInvolutiveSSet.{u} :=
  fun _ _ f ↦ AntiInvolutiveSSet.NormalMono f

/-- The literal whole generator belongs to both exact requested source classes. -/
theorem tagged_normal_and_weak :
    (normalCofibrations ⊓ DaggerActualAntiJoyalMappingWeakProperties.weakEquivalences)
      taggedGenerator.{u} :=
  ⟨taggedGenerator_normal,
    DaggerActualTaggedWalkingJoyalMappingWeak.taggedGenerator_weakCategoricalEquivalence⟩

/-- The class obstruction uses the actual standard dagger model, without a source model input. -/
theorem leftKan_not_preserves_normal_weak :
    ¬ (normalCofibrations ⊓ DaggerActualAntiJoyalMappingWeakProperties.weakEquivalences ≤
      (weakEquivalences DaggerSSet.{u}).inverseImage leftKan) := by
  intro h
  exact imageGenerator_not_weak ((weakEquivalence_iff _).2 (h _ tagged_normal_and_weak))

/-- Consequently the exact source trivial classes cannot land in actual dagger trivial cofibrations. -/
theorem leftKan_not_preserves_trivial_classes :
    ¬ (normalCofibrations ⊓ DaggerActualAntiJoyalMappingWeakProperties.weakEquivalences ≤
      (trivialCofibrations DaggerSSet.{u}).inverseImage leftKan) := by
  intro h
  apply leftKan_not_preserves_normal_weak
  intro X Y f hf
  exact (h f hf).2

end
end DaggerActualTaggedJoyalClassObstruction
