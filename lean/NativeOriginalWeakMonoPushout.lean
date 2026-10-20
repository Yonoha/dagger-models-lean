import NativeIhomPushoutPullback
import NativeOriginalCorePullbackWeak

/-! The full original Joyal weak mono class is stable under every actual pushout. -/
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory HomotopicalAlgebra
open DaggerOriginalOrdinaryKanCoreSubcomplex DaggerNativeJoyalMappingTest
open DaggerNativeIhomQuasicategories DaggerNativeWeakRestrictionCoreTrivialFibration
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeOriginalWeakMonoPushout
noncomputable section

theorem weak_of_isPushout {A B C D : SSet.{u}} {i : A ⟶ B} {a : A ⟶ C}
    {b : B ⟶ D} {j : C ⟶ D} (h : IsPushout i a b j) [Mono i]
    (hi : weakCategoricalEquivalences i) : weakCategoricalEquivalences j := by
  apply (DaggerNativeCoreMappingWeakRecognition.weak_iff_core_mapping_weak j).mpr
  intro Z _
  have : ((ihom C).obj Z).Quasicategory := ihom_quasicategory C Z
  have ht := weak_mono_core_trivial i hi Z
  have : Fibration (ordinaryCoreCandidateMap ((MonoidalClosed.pre i).app Z)) :=
    (mem_trivialFibrations_iff _).mp ht |>.1
  have : WeakEquivalence (ordinaryCoreCandidateMap ((MonoidalClosed.pre i).app Z)) :=
    (mem_trivialFibrations_iff _).mp ht |>.2
  exact DaggerNativeOriginalCorePullbackWeak.square_projection_weak
    (DaggerNativeIhomPushoutPullback.isPullback h Z)

theorem weak_mono_of_isPushout {A B C D : SSet.{u}} {i : A ⟶ B} {a : A ⟶ C}
    {b : B ⟶ D} {j : C ⟶ D} (h : IsPushout i a b j)
    (hi : (MorphismProperty.monomorphisms SSet.{u} ⊓ weakCategoricalEquivalences) i) :
    (MorphismProperty.monomorphisms SSet.{u} ⊓ weakCategoricalEquivalences) j := by
  have : Mono i := hi.1
  have : Cofibration i := SSet.modelCategoryQuillen.cofibration_of_mono i
  have hj : cofibrations SSet.{u} j :=
    MorphismProperty.of_isPushout h.flip ((cofibration_iff i).mp inferInstance)
  have : Cofibration j := (cofibration_iff j).mpr hj
  exact ⟨(SSet.modelCategoryQuillen.cofibration_iff j).mp inferInstance,
    weak_of_isPushout h hi.2⟩

end
end DaggerNativeOriginalWeakMonoPushout
