import ActualTaggedJoyalClassObstruction

/-!
# Both original adjunctions fail for every model with the exact DCH classes

Derive the literal walking generator trivial-cofibration fact from the two exact
class identities. No generator weakness/triviality premise remains. The source
model itself and both full class identities remain explicit: this theorem does
not claim the still missing DCH model existence construction.
-/
set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra DaggerModels
open DaggerModels.OriginalTaggedReverseAdjunctions
open DaggerActualTaggedWalkingIsoImageDKObstruction
open DaggerActualTaggedWalkingIsoSourceHomotopy
open DaggerActualTaggedObstructionsForStandardDaggerModel
universe u
namespace DaggerActualTaggedNonQuillenForExactDCHClasses
noncomputable section

local instance : ModelCategory DaggerSSet.{u} := DaggerActualRigidificationQuillen.modelD.{u}
variable [ModelCategory AntiInvolutiveSSet.{u}]

/-- The original whole generator is trivial solely from the exact source class identities. -/
theorem tagged_trivial_of_exact_classes
    (hc : ∀ {X Y : AntiInvolutiveSSet.{u}} (f : X ⟶ Y),
      Cofibration f ↔ AntiInvolutiveSSet.NormalMono f)
    (hw : ∀ {X Y : AntiInvolutiveSSet.{u}} (f : X ⟶ Y),
      WeakEquivalence f ↔ DaggerActualAntiJoyalMappingWeakProperties.weakEquivalences f) :
    trivialCofibrations AntiInvolutiveSSet.{u} taggedGenerator.{u} :=
  (mem_trivialCofibrations_iff _).2
    ⟨(hc _).2 taggedGenerator_normal,
      (hw _).2 DaggerActualTaggedJoyalClassObstruction.tagged_normal_and_weak.2⟩

/-- Both actual adjunctions fail with the actual target model and the exact full source classes. -/
theorem both_not_quillen_for_exact_classes
    (hc : ∀ {X Y : AntiInvolutiveSSet.{u}} (f : X ⟶ Y),
      Cofibration f ↔ AntiInvolutiveSSet.NormalMono f)
    (hw : ∀ {X Y : AntiInvolutiveSSet.{u}} (f : X ⟶ Y),
      WeakEquivalence f ↔ DaggerActualAntiJoyalMappingWeakProperties.weakEquivalences f) :
    ¬ leftAdjunction.{u}.IsQuillenAdjunction ∧ ¬ rightAdjunction.{u}.IsQuillenAdjunction :=
  ⟨left_not_quillen (tagged_trivial_of_exact_classes hc hw), right_not_quillen hc⟩

end
end DaggerActualTaggedNonQuillenForExactDCHClasses
