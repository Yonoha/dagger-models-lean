import NativeFreePathPairingRegularity
import NativeInnerPairing
import NativeInnerJoyalMappingWeak

/-! Reuse the existing regular inner pairing on the SAME original free-path generator spine. -/
set_option autoImplicit false
open CategoryTheory Simplicial
open DaggerNativeFreePathNerveWeight DaggerNativeFreePathPairingCore
open DaggerNativeFreePathPairingRegularity DaggerNativeInnerPairing
open DaggerNativeInnerHornFactorization DaggerNativeJoyalMappingTest
universe u
namespace DaggerNativeFreePathSpineInner
noncomputable section

variable (V : Type u) [Quiver.{u + 1} V]

theorem generatorSpine_innerAnodyne : innerAnodyne (generatorSpine V).ι :=
  pairing_innerAnodyne (pairingCore V).pairing (pairingCoreInner V).pairing

theorem generatorSpine_categorical_weak : weakCategoricalEquivalences (generatorSpine V).ι :=
  DaggerNativeInnerJoyalMappingWeak.innerAnodyne_weak _ (generatorSpine_innerAnodyne V)

end
end DaggerNativeFreePathSpineInner
