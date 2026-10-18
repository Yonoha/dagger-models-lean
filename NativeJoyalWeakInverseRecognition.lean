import NativeJoyalWeakQuasiInverse
import NativeIhomHoPreAction
import NativeInnerQuasicategoryWeakReplacement

/-!
# The complete fixed mapping weak class is detected by actual inverse data after replacement

Both native ho isomorphisms act on the entire original precomposition functors.
The native equivalence keeps precomposition by f as its forward functor. Combine
the quasi-category characterization with the already proved original whole inner
replacement preservation and reflection to characterize every original map.
-/
set_option autoImplicit false
open CategoryTheory
open DaggerNativeWalkingRetractionMappingEquivalence DaggerNativeIhomHoObjects
open DaggerNativeIhomHoPreAction DaggerNativeJoyalWeakQuasiInverse
open DaggerNativeJoyalMappingTest
universe u
namespace DaggerNativeJoyalWeakInverseRecognition
noncomputable section

def mappingEquivalence {A B : SSet.{u}} (f : A ⟶ B) (d : InverseData f)
    (Z : SSet.{u}) :
    SSet.hoFunctor.obj ((ihom B).obj Z) ≌ SSet.hoFunctor.obj ((ihom A).obj Z) :=
  CategoryTheory.Equivalence.mk (preHoFunctor f Z) (preHoFunctor d.inv Z)
    ((eqToIso (preHoFunctor_id B Z)).symm ≪≫
      (preIso (d.inv ≫ f) (𝟙 B) d.rightIso Z).symm ≪≫
      (eqToIso (preHoFunctor_comp d.inv f Z)).symm)
    (eqToIso (preHoFunctor_comp f d.inv Z) ≪≫
      preIso (f ≫ d.inv) (𝟙 A) d.leftIso Z ≪≫ eqToIso (preHoFunctor_id A Z))

theorem inverse_data_weak {A B : SSet.{u}} (f : A ⟶ B) (d : InverseData f) :
    weakCategoricalEquivalences f := fun Z _ ↦
  show (mappingEquivalence f d Z).functor.IsEquivalence by infer_instance

theorem quasi_weak_iff_inverse_data {A B : SSet.{u}} [A.Quasicategory] [B.Quasicategory]
    (f : A ⟶ B) : weakCategoricalEquivalences f ↔ Nonempty (InverseData f) := by
  constructor
  · exact exists_inverse_data f
  · rintro ⟨d⟩
    exact inverse_data_weak f d

theorem weak_iff_replacement_inverse_data {A B : SSet.{u}} (f : A ⟶ B) :
    weakCategoricalEquivalences f ↔
      Nonempty (InverseData (DaggerNativeInnerHornFactorization.replacement.map f)) := by
  exact (DaggerNativeInnerQuasicategoryWeakReplacement.replacement_map_weak_iff f).symm.trans
    (quasi_weak_iff_inverse_data (DaggerNativeInnerHornFactorization.replacement.map f))

end
end DaggerNativeJoyalWeakInverseRecognition
