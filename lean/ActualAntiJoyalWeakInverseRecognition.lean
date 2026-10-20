import NativeJoyalWeakInverseRecognition
import ActualAntiInnerWeakReplacement

/-!
# The full actual anti-involutive weak class has the same underlying inverse-data test

Use the existing actual anti-inner replacement, with its normal weak unit and
quasi-categorical underlying objects. The actual map and its entire underlying
replacement map are retained. The inverse is an ordinary underlying map; it is
not asserted to preserve the anti-involution.
-/
set_option autoImplicit false
open CategoryTheory DaggerModels
open DaggerNativeJoyalWeakQuasiInverse DaggerNativeJoyalWeakInverseRecognition
open DaggerActualAntiJoyalMappingWeakProperties
universe u
namespace DaggerActualAntiJoyalWeakInverseRecognition

theorem weak_iff_replacement_underlying_inverse_data {A B : AntiInvolutiveSSet.{u}}
    (f : A ⟶ B) : weakEquivalences f ↔
      Nonempty (InverseData
        (DaggerActualAntiInnerHornFactorization.replacement.map f).hom) := by
  exact (DaggerActualAntiInnerWeakReplacement.replacement_map_weak_iff f).symm.trans
    (quasi_weak_iff_inverse_data
      (DaggerActualAntiInnerHornFactorization.replacement.map f).hom)

end DaggerActualAntiJoyalWeakInverseRecognition
