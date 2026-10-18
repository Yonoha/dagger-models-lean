import NativeWalkingEndpointTrivialRestriction

/-! Every full native mono restriction into a quasi-category lifts the original zero-J endpoint. -/
set_option autoImplicit false
open CategoryTheory Limits Simplicial MonoidalCategory
open DaggerActualFreeWalkingIsoIntegerObstruction DaggerNativeInnerJoyalMappingWeak
open DaggerNativeWalkingEndpointTrivialRestriction
universe u
namespace DaggerNativeMonoRestrictionWalkingLifting
noncomputable section

theorem pushout_zero_lifting {A B : SSet.{u}} (i : A ⟶ B) [Mono i]
    (Z : SSet.{u}) [Z.Quasicategory] (sq : SSet.PushoutTensor i zeroInclusion.{u}) :
    HasLiftingProperty sq.ι (terminal.from Z) := by
  let pb := terminalPullback zeroInclusion.{u} Z
  have hh : HasLiftingProperty i pb.π := by
    simpa only [pb, terminalPullback_π] using
      endpoint_mono_rlp Z i (show Mono i from inferInstance)
  rw [← SSet.hasLiftingProperty_iff_of_pushoutTensor_of_pullbackIhom sq.flip pb,
    HasLiftingProperty.iff_of_arrow_iso_left sq.flipArrowIso] at hh
  exact hh

theorem restriction_zero_lifting {A B : SSet.{u}} (i : A ⟶ B) [Mono i]
    (Z : SSet.{u}) [Z.Quasicategory] :
    HasLiftingProperty zeroInclusion.{u} ((MonoidalClosed.pre i).app Z) := by
  let sq : SSet.PushoutTensor i zeroInclusion.{u} := Functor.PushoutObjObj.ofHasPushout _ _ _
  have hh := (SSet.hasLiftingProperty_iff_of_pushoutTensor_of_pullbackIhom sq
    (terminalPullback i Z)).mp (pushout_zero_lifting i Z sq)
  simpa only [terminalPullback_π] using hh

end
end DaggerNativeMonoRestrictionWalkingLifting
