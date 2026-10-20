import NativeOriginalJoyalSmithModelData
import ActualAntiJoyalAdjointLifting

/-! Full original weak normal closure on the actual anti-involutive category. -/
set_option autoImplicit false
open CategoryTheory Limits DaggerModels MorphismProperty
open DaggerModels.OriginalTaggedReverseFreeCompletion
open DaggerModels.OriginalAntiInvolutiveNormalMonoSaturation
open DaggerActualAntiJoyalMappingWeakProperties DaggerActualAntiNormalFactorization
open DaggerActualAntiJoyalAdjointLifting
universe u
namespace DaggerActualOriginalAntiWeakNormalClosure
noncomputable section

instance forgetWellOrder (J : Type u) [LinearOrder J] :
    PreservesWellOrderContinuousOfShape J antiForget.{u} where

instance normalCobaseChange : normalMonos.{u}.IsStableUnderCobaseChange := by
  rw [normalMonos_eq_generators_rlp_llp]
  infer_instance

instance normalTransfinite : IsStableUnderTransfiniteComposition.{u} normalMonos.{u} where
  isStableUnderTransfiniteCompositionOfShape J _ _ _ _ := by
    rw [normalMonos_eq_generators_rlp_llp]
    infer_instance

theorem weak_normal_of_isPushout {A B C D : AntiInvolutiveSSet.{u}}
    {i : A ⟶ B} {a : A ⟶ C} {b : B ⟶ D} {j : C ⟶ D}
    (h : IsPushout i a b j) (hi : (normalMonos ⊓ weakEquivalences) i) :
    (normalMonos ⊓ weakEquivalences) j := by
  have hn : normalMonos j := MorphismProperty.of_isPushout h.flip hi.1
  have hw := DaggerNativeOriginalWeakMonoPushout.weak_mono_of_isPushout
    (h.map antiForget) (forget_normal_weak i hi)
  exact ⟨hn, hw.2⟩

instance weakNormalCobaseChange :
    (normalMonos.{u} ⊓ weakEquivalences).IsStableUnderCobaseChange where
  of_isPushout h hi := weak_normal_of_isPushout h.flip hi

theorem transfinite_shape (J : Type u) [LinearOrder J] [SuccOrder J] [OrderBot J]
    [WellFoundedLT J] :
    IsStableUnderTransfiniteCompositionOfShape (normalMonos.{u} ⊓ weakEquivalences) J := by
  constructor
  intro A B i hi
  obtain ⟨h⟩ := hi
  have hn : normalMonos i := normalMonos.transfiniteCompositionsOfShape_le J i
    ⟨h.ofLE inf_le_left⟩
  let Q := monomorphisms SSet.{u} ⊓ DaggerNativeJoyalMappingTest.weakCategoricalEquivalences
  have hu : (Q.inverseImage antiForget).TransfiniteCompositionOfShape J i :=
    h.ofLE (fun _ _ f hf ↦ forget_normal_weak f hf)
  have hw : Q (antiForget.map i) := Q.transfiniteCompositionsOfShape_le J _ ⟨hu.map⟩
  exact ⟨hn, hw.2⟩

instance weakNormalTransfinite :
    IsStableUnderTransfiniteComposition.{u} (normalMonos.{u} ⊓ weakEquivalences) where
  isStableUnderTransfiniteCompositionOfShape J _ _ _ _ := transfinite_shape J

end
end DaggerActualOriginalAntiWeakNormalClosure
