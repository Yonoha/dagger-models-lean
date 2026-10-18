import NativeOriginalWeakMonoLiftingRecognition

/-! Full original weak mono closure for every transfinite composition in the model universe. -/
set_option autoImplicit false
open CategoryTheory MorphismProperty
open DaggerNativeJoyalMappingTest DaggerNativeOriginalWeakMonoLiftingRecognition
universe u
namespace DaggerNativeOriginalWeakMonoTransfinite
noncomputable section

theorem transfinite_shape (J : Type u) [LinearOrder J] [SuccOrder J] [OrderBot J]
    [WellFoundedLT J] :
    IsStableUnderTransfiniteCompositionOfShape
      (monomorphisms SSet.{u} ⊓ weakCategoricalEquivalences) J := by
  rw [weak_mono_eq]
  constructor
  intro A B i hi
  obtain ⟨h⟩ := hi
  exact ⟨(monomorphisms SSet.{u}).transfiniteCompositionsOfShape_le J i
      ⟨h.ofLE inf_le_left⟩,
    tests.llp.transfiniteCompositionsOfShape_le J i ⟨h.ofLE inf_le_right⟩⟩

instance stableCobaseChange :
    (monomorphisms SSet.{u} ⊓ weakCategoricalEquivalences).IsStableUnderCobaseChange where
  of_isPushout h hi := DaggerNativeOriginalWeakMonoPushout.weak_mono_of_isPushout h.flip hi

instance stableTransfinite :
    IsStableUnderTransfiniteComposition.{u}
      (monomorphisms SSet.{u} ⊓ weakCategoricalEquivalences) where
  isStableUnderTransfiniteCompositionOfShape J _ _ _ _ := transfinite_shape J

theorem transfinite_weak_mono {A B : SSet.{u}} (i : A ⟶ B)
    (hi : transfiniteCompositions.{u}
      (monomorphisms SSet.{u} ⊓ weakCategoricalEquivalences) i) :
    (monomorphisms SSet.{u} ⊓ weakCategoricalEquivalences) i :=
  transfiniteCompositions_le _ _ hi

end
end DaggerNativeOriginalWeakMonoTransfinite
