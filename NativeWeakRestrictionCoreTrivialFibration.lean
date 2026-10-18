import NativeOriginalCoreWalkingInverse
import NativeRelativeWalkingCoreFibration
import NativeJoyalWeakRestriction

/-! Original weak mono restrictions give native Kan trivial fibrations on the same exact cores. -/
set_option autoImplicit false
open CategoryTheory MonoidalCategory HomotopicalAlgebra
open DaggerOriginalOrdinaryKanCoreSubcomplex DaggerNativeIhomQuasicategories
open DaggerNativeOriginalCoreWalkingInverse DaggerNativeRelativeWalkingCoreFibration
open DaggerNativeJoyalMappingTest DaggerNativeJoyalWeakRestriction
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeWeakRestrictionCoreTrivialFibration
noncomputable section

theorem weak_restriction_core_Kan_weak {A B : SSet.{u}} (i : A ⟶ B)
    (hi : weakCategoricalEquivalences i) (Z : SSet.{u}) [Z.Quasicategory] :
    WeakEquivalence (ordinaryCoreCandidateMap ((MonoidalClosed.pre i).app Z)) := by
  have : ((ihom A).obj Z).Quasicategory := ihom_quasicategory A Z
  have : ((ihom B).obj Z).Quasicategory := ihom_quasicategory B Z
  exact weak_core_map _ (restriction_weak i hi Z)

theorem weak_mono_core_trivial {A B : SSet.{u}} (i : A ⟶ B) [Mono i]
    (hi : weakCategoricalEquivalences i) (Z : SSet.{u}) [Z.Quasicategory] :
    trivialFibrations SSet.{u} (ordinaryCoreCandidateMap ((MonoidalClosed.pre i).app Z)) :=
  (mem_trivialFibrations_iff _).mpr
    ⟨mono_restriction_core_fibration i Z, weak_restriction_core_Kan_weak i hi Z⟩

theorem weak_mono_core_mono_rlp {A B : SSet.{u}} (i : A ⟶ B) [Mono i]
    (hi : weakCategoricalEquivalences i) (Z : SSet.{u}) [Z.Quasicategory] :
    (MorphismProperty.monomorphisms SSet.{u}).rlp
      (ordinaryCoreCandidateMap ((MonoidalClosed.pre i).app Z)) := by
  have ht := weak_mono_core_trivial i hi Z
  have : Fibration (ordinaryCoreCandidateMap ((MonoidalClosed.pre i).app Z)) :=
    (mem_trivialFibrations_iff _).mp ht |>.1
  have : WeakEquivalence (ordinaryCoreCandidateMap ((MonoidalClosed.pre i).app Z)) :=
    (mem_trivialFibrations_iff _).mp ht |>.2
  intro K L j hj
  have : Mono j := hj
  have : Cofibration j := (SSet.modelCategoryQuillen.cofibration_iff _).mpr inferInstance
  infer_instance

end
end DaggerNativeWeakRestrictionCoreTrivialFibration
