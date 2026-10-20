import ActualAntiForgetAdjointTriple

/-!
# Small limits and colimits in the original anti-involutive category

Transport the actual presheaf limits and colimits across the established
anti-involutive presheaf equivalence. No model-structure input is involved.
-/
set_option autoImplicit false
open CategoryTheory Limits DaggerModels
open DaggerModels.OriginalTaggedReversePresheafInclusion
universe u
namespace DaggerActualAntiInvolutiveLimits
noncomputable section

local instance presheafEquivalence : antiInvolutiveEquivalence.{u}.functor.IsEquivalence := by
  infer_instance

private instance (J : Type u) [Category.{u} J] :
    HasLimitsOfShape J AntiInvolutiveSSet.{u} :=
  Adjunction.hasLimitsOfShape_of_equivalence antiInvolutiveEquivalence.functor

private instance (J : Type u) [Category.{u} J] :
    HasColimitsOfShape J AntiInvolutiveSSet.{u} :=
  Adjunction.hasColimitsOfShape_of_equivalence antiInvolutiveEquivalence.functor

instance antiHasLimits : HasLimitsOfSize.{u, u} AntiInvolutiveSSet.{u} :=
  ⟨fun _ _ ↦ inferInstance⟩

instance antiHasColimits : HasColimitsOfSize.{u, u} AntiInvolutiveSSet.{u} :=
  ⟨fun _ _ ↦ inferInstance⟩

instance antiHasFiniteLimits : HasFiniteLimits AntiInvolutiveSSet.{u} :=
  hasFiniteLimits_of_hasLimitsOfSize _

instance antiHasFiniteColimits : HasFiniteColimits AntiInvolutiveSSet.{u} :=
  hasFiniteColimits_of_hasColimitsOfSize _

end
end DaggerActualAntiInvolutiveLimits
