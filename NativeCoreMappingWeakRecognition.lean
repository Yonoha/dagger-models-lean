import NativeCoreMappingQuasiRecognition
import NativeInnerQuasicategoryWeakReplacement

/-! The full original all-target mapping weak class is equivalent to exact core mapping tests. -/
set_option autoImplicit false
open CategoryTheory MonoidalCategory HomotopicalAlgebra
open DaggerOriginalOrdinaryKanCoreSubcomplex DaggerNativeOriginalCoreWalkingInverse
open DaggerNativeJoyalMappingTest DaggerNativeIhomQuasicategories
open DaggerNativeInnerHornFactorization DaggerNativeInnerJoyalMappingWeak
open DaggerNativeWeakRestrictionCoreTrivialFibration
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeCoreMappingWeakRecognition
noncomputable section

theorem core_pre_comp {A B C : SSet.{u}} (f : A ⟶ B) (g : B ⟶ C) (Z : SSet.{u}) :
    ordinaryCoreCandidateMap ((MonoidalClosed.pre (f ≫ g)).app Z) =
      ordinaryCoreCandidateMap ((MonoidalClosed.pre g).app Z) ≫
        ordinaryCoreCandidateMap ((MonoidalClosed.pre f).app Z) := by
  rw [MonoidalClosed.pre_map, NatTrans.comp_app, core_map_comp]

theorem replacement_core_test_weak {A B : SSet.{u}} (f : A ⟶ B)
    (h : ∀ (Z : SSet.{u}) [Z.Quasicategory],
      WeakEquivalence (ordinaryCoreCandidateMap ((MonoidalClosed.pre f).app Z)))
    (Z : SSet.{u}) [Z.Quasicategory] :
    WeakEquivalence
      (ordinaryCoreCandidateMap ((MonoidalClosed.pre (replacement.map f)).app Z)) := by
  have : WeakEquivalence
      (ordinaryCoreCandidateMap ((MonoidalClosed.pre (unit.app A)).app Z)) :=
    weak_restriction_core_Kan_weak _ (unit_weak A) Z
  have : WeakEquivalence
      (ordinaryCoreCandidateMap ((MonoidalClosed.pre (unit.app B)).app Z)) :=
    weak_restriction_core_Kan_weak _ (unit_weak B) Z
  have : WeakEquivalence (ordinaryCoreCandidateMap ((MonoidalClosed.pre f).app Z)) := h Z
  have hs := congrArg (fun k : A ⟶ replacement.obj B ↦
    ordinaryCoreCandidateMap ((MonoidalClosed.pre k).app Z)) (unit.naturality f)
  change ordinaryCoreCandidateMap ((MonoidalClosed.pre (f ≫ unit.app B)).app Z) =
    ordinaryCoreCandidateMap ((MonoidalClosed.pre (unit.app A ≫ replacement.map f)).app Z) at hs
  rw [core_pre_comp, core_pre_comp] at hs
  exact weakEquivalence_of_postcomp_of_fac hs.symm

theorem weak_iff_core_mapping_weak {A B : SSet.{u}} (f : A ⟶ B) :
    weakCategoricalEquivalences f ↔ ∀ (Z : SSet.{u}) [Z.Quasicategory],
      WeakEquivalence (ordinaryCoreCandidateMap ((MonoidalClosed.pre f).app Z)) := by
  constructor
  · exact fun hf Z _ ↦ weak_restriction_core_Kan_weak f hf Z
  · intro h
    apply (DaggerNativeInnerQuasicategoryWeakReplacement.replacement_map_weak_iff f).mp
    apply (DaggerNativeCoreMappingQuasiRecognition.quasi_weak_iff_core_mapping_weak _).mpr
    exact replacement_core_test_weak f h

end
end DaggerNativeCoreMappingWeakRecognition
