import NativeOriginalWeakMonoPushout
import NativeWeakMonoQuasicategoryExtension
import NativeJoyalMappingTensor

/-! Every actual pushout-tensor of an original weak mono is original weak. -/
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory HomotopicalAlgebra
open DaggerNativeJoyalMappingTest DaggerNativeJoyalMappingTensor
open DaggerNativeOriginalWeakMonoPushout
universe u
namespace DaggerNativeOriginalWeakPushoutTensor
noncomputable section

theorem pushout_tensor_weak {A B K L : SSet.{u}} (i : A ⟶ B) [Mono i]
    (hi : weakCategoricalEquivalences i) (j : K ⟶ L) (sq : SSet.PushoutTensor i j) :
    weakCategoricalEquivalences sq.ι := by
  have hiK := weak_whiskerRight i hi K
  have hiL := weak_whiskerRight i hi L
  have : Mono (((curriedTensor SSet).map i).app K) :=
    DaggerNativeMonoRestrictionParameterizedWalkingLifting.right_tensor_mono i K
  have hr : weakCategoricalEquivalences sq.inr := weak_of_isPushout sq.isPushout hiK
  apply weakCategoricalEquivalences.of_precomp sq.inr sq.ι hr
  have he : sq.inr ≫ sq.ι = i ▷ L := sq.inr_ι
  rw [he]
  exact hiL

end
end DaggerNativeOriginalWeakPushoutTensor
