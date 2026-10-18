import NativeHoIsoWholeWalkingHomotopy
import NativeJoyalWeakInverseRecognition
import NativeWalkingTwoSidedMappingEquivalence

/-! The unchanged mapping weak class has whole J-cylinder inverses between quasi-categories. -/
set_option autoImplicit false
open CategoryTheory MonoidalCategory
open DaggerActualFreeWalkingIsoIntegerObstruction DaggerActualFreeAntiWalkingCategoricalCylinder
open DaggerNativeHoIsoWholeWalkingHomotopy DaggerNativeJoyalMappingTest
open DaggerNativeJoyalWeakQuasiInverse
universe u
namespace DaggerNativeJoyalWeakWholeWalkingInverse
noncomputable section

structure WalkingInverseData {A B : SSet.{u}} (f : A ⟶ B) where
  inv : B ⟶ A
  leftCylinder : A ⊗ J.{u} ⟶ A
  rightCylinder : B ⊗ J.{u} ⟶ B
  left_zero : intervalEndpoint A false ≫ leftCylinder = f ≫ inv
  left_one : intervalEndpoint A true ≫ leftCylinder = 𝟙 A
  right_zero : intervalEndpoint B false ≫ rightCylinder = inv ≫ f
  right_one : intervalEndpoint B true ≫ rightCylinder = 𝟙 B

def fromWeak {A B : SSet.{u}} [A.Quasicategory] [B.Quasicategory] (f : A ⟶ B)
    (hf : weakCategoricalEquivalences f) : WalkingInverseData f := by
  let d := DaggerNativeJoyalWeakQuasiInverse.fromWeak f hf
  let l := exists_homotopy (f ≫ d.inv) (𝟙 A) d.leftIso
  let r := exists_homotopy (d.inv ≫ f) (𝟙 B) d.rightIso
  exact ⟨d.inv, l.choose, r.choose, l.choose_spec.1, l.choose_spec.2,
    r.choose_spec.1, r.choose_spec.2⟩

theorem walking_inverse_weak {A B : SSet.{u}} (f : A ⟶ B) (d : WalkingInverseData f) :
    weakCategoricalEquivalences f :=
  DaggerNativeWalkingTwoSidedMappingEquivalence.weak f d.inv d.leftCylinder d.rightCylinder
    d.left_zero d.left_one d.right_zero d.right_one

theorem quasi_weak_iff_whole_walking_inverse {A B : SSet.{u}}
    [A.Quasicategory] [B.Quasicategory] (f : A ⟶ B) :
    weakCategoricalEquivalences f ↔ Nonempty (WalkingInverseData f) :=
  ⟨fun hf ↦ ⟨fromWeak f hf⟩, fun ⟨d⟩ ↦ walking_inverse_weak f d⟩

end
end DaggerNativeJoyalWeakWholeWalkingInverse
