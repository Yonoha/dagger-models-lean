import NativeOriginalCoreComponents
import NativeJoyalWeakInverseRecognition
import NativeWeakRestrictionCoreTrivialFibration

/-! Two exact original core-component tests recover full original inverse data. -/
set_option autoImplicit false
open CategoryTheory MonoidalCategory HomotopicalAlgebra
open DaggerOriginalOrdinaryKanCoreSubcomplex DaggerNativeOriginalCoreComponents
open DaggerNativeIhomHoObjects DaggerNativeJoyalWeakQuasiInverse
open DaggerNativeJoyalMappingTest DaggerNativeIhomQuasicategories
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeCoreMappingQuasiRecognition
noncomputable section

def inverseData {A B : SSet.{u}} (f : A ⟶ B) [A.Quasicategory] [B.Quasicategory]
    (hA : Function.Surjective
      (SSet.mapπ₀ (ordinaryCoreCandidateMap ((MonoidalClosed.pre f).app A))))
    (hB : Function.Injective
      (SSet.mapπ₀ (ordinaryCoreCandidateMap ((MonoidalClosed.pre f).app B)))) :
    InverseData f := by
  let c := (hA (component (𝟙 A))).choose
  have hc := (hA (component (𝟙 A))).choose_spec
  let g := (component_surjective B A c).choose
  have hg : component g = c := (component_surjective B A c).choose_spec
  change SSet.mapπ₀ (ordinaryCoreCandidateMap ((MonoidalClosed.pre f).app A)) c = _ at hc
  rw [← hg, pre_component] at hc
  let eA := ((component_eq_iff (f ≫ g) (𝟙 A)).mp hc).some
  have eFB : homObject (f ≫ (g ≫ f)) ≅ homObject (f ≫ 𝟙 B) := by
    rw [Category.comp_id]
    exact eqToIso (congrArg (fun h : A ⟶ B ↦ homObject h) (Category.assoc f g f).symm) ≪≫
      (eqToIso (post_obj (f ≫ g) f)).symm ≪≫ (postHoFunctor A f).mapIso eA ≪≫
      eqToIso (post_obj (𝟙 A) f) ≪≫
      eqToIso (congrArg (fun h : A ⟶ B ↦ homObject h) (Category.id_comp f))
  have hcB : component (g ≫ f) = component (𝟙 B) := by
    apply hB
    rw [pre_component, pre_component]
    exact (component_eq_iff _ _).mpr ⟨eFB⟩
  exact ⟨g, eA, ((component_eq_iff _ _).mp hcB).some⟩

theorem weak_of_two_component_tests {A B : SSet.{u}} (f : A ⟶ B)
    [A.Quasicategory] [B.Quasicategory]
    (hA : Function.Surjective
      (SSet.mapπ₀ (ordinaryCoreCandidateMap ((MonoidalClosed.pre f).app A))))
    (hB : Function.Injective
      (SSet.mapπ₀ (ordinaryCoreCandidateMap ((MonoidalClosed.pre f).app B)))) :
    weakCategoricalEquivalences f :=
  DaggerNativeJoyalWeakInverseRecognition.inverse_data_weak f (inverseData f hA hB)

theorem quasi_weak_iff_core_mapping_weak {A B : SSet.{u}}
    [A.Quasicategory] [B.Quasicategory] (f : A ⟶ B) :
    weakCategoricalEquivalences f ↔ ∀ (Z : SSet.{u}) [Z.Quasicategory],
      WeakEquivalence (ordinaryCoreCandidateMap ((MonoidalClosed.pre f).app Z)) := by
  constructor
  · exact fun hf Z _ ↦
      DaggerNativeWeakRestrictionCoreTrivialFibration.weak_restriction_core_Kan_weak f hf Z
  · intro h
    have : ((ihom A).obj A).Quasicategory := ihom_quasicategory A A
    have : ((ihom B).obj A).Quasicategory := ihom_quasicategory B A
    have : ((ihom A).obj B).Quasicategory := ihom_quasicategory A B
    have : ((ihom B).obj B).Quasicategory := ihom_quasicategory B B
    exact weak_of_two_component_tests f
      (weak_core_bijective_components _ (h A)).2
      (weak_core_bijective_components _ (h B)).1

end
end DaggerNativeCoreMappingQuasiRecognition
