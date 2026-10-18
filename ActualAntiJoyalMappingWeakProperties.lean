import NativeJoyalMappingWeakProperties
import OriginalTaggedReverseFreeCompletion

/-!
# The exact underlying Joyal mapping weak class on the original anti-involutive category

This fixes the requested right-induced weak class and proves its basic closure
properties. It is not a claim that either model factorization is constructed.
-/
set_option autoImplicit false
open CategoryTheory DaggerModels
open DaggerModels.OriginalTaggedReverseFreeCompletion
universe u
namespace DaggerActualAntiJoyalMappingWeakProperties

/-- The actual original forgetful functor creates this exact underlying Joyal weak class. -/
def weakEquivalences : MorphismProperty AntiInvolutiveSSet.{u} :=
  DaggerNativeJoyalMappingTest.weakCategoricalEquivalences.inverseImage antiForget

theorem weak_iff_underlying {X Y : AntiInvolutiveSSet.{u}} (f : X ⟶ Y) :
    weakEquivalences f ↔
      DaggerNativeJoyalMappingTest.weakCategoricalEquivalences f.hom := Iff.rfl

instance containsIdentities : weakEquivalences.{u}.ContainsIdentities := by
  unfold weakEquivalences
  infer_instance

instance twoOutOfThree : weakEquivalences.{u}.HasTwoOutOfThreeProperty := by
  unfold weakEquivalences
  infer_instance

instance stableRetracts : weakEquivalences.{u}.IsStableUnderRetracts := by
  unfold weakEquivalences
  infer_instance

end DaggerActualAntiJoyalMappingWeakProperties
