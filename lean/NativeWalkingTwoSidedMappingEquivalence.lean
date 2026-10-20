import NativeWalkingRetractionMappingEquivalence
import NativeJoyalMappingTest

/-!
# Whole two-sided original J-homotopies imply the fixed mapping weak predicate

Keep both entire original cylinders and their endpoint equations. The forward
functor is exactly native ho of actual internal-Hom precomposition by g.
-/
set_option autoImplicit false
open CategoryTheory MonoidalCategory
open DaggerActualFreeWalkingIsoIntegerObstruction
open DaggerActualFreeAntiWalkingCategoricalCylinder
open DaggerNativeWalkingRetractionMappingEquivalence
universe u
namespace DaggerNativeWalkingTwoSidedMappingEquivalence
noncomputable section

def mappingEquivalence {A B : SSet.{u}} (g : A ⟶ B) (r : B ⟶ A)
    (HA : A ⊗ J ⟶ A) (HB : B ⊗ J ⟶ B)
    (hA₀ : intervalEndpoint A false ≫ HA = g ≫ r)
    (hA₁ : intervalEndpoint A true ≫ HA = 𝟙 A)
    (hB₀ : intervalEndpoint B false ≫ HB = r ≫ g)
    (hB₁ : intervalEndpoint B true ≫ HB = 𝟙 B) (Z : SSet.{u}) :
    SSet.hoFunctor.obj ((ihom B).obj Z) ≌ SSet.hoFunctor.obj ((ihom A).obj Z) :=
  CategoryTheory.Equivalence.mk (preHoFunctor g Z) (preHoFunctor r Z)
    ((eqToIso (preHoFunctor_id B Z)).symm ≪≫
      (preRetractionIso g r HB hB₀ hB₁ Z).symm ≪≫
      (eqToIso (preHoFunctor_comp r g Z)).symm)
    (eqToIso (preHoFunctor_comp g r Z) ≪≫
      preRetractionIso r g HA hA₀ hA₁ Z ≪≫ eqToIso (preHoFunctor_id A Z))

theorem preHoFunctor_isEquivalence {A B : SSet.{u}} (g : A ⟶ B) (r : B ⟶ A)
    (HA : A ⊗ J ⟶ A) (HB : B ⊗ J ⟶ B)
    (hA₀ : intervalEndpoint A false ≫ HA = g ≫ r)
    (hA₁ : intervalEndpoint A true ≫ HA = 𝟙 A)
    (hB₀ : intervalEndpoint B false ≫ HB = r ≫ g)
    (hB₁ : intervalEndpoint B true ≫ HB = 𝟙 B) (Z : SSet.{u}) :
    (preHoFunctor g Z).IsEquivalence :=
  show (mappingEquivalence g r HA HB hA₀ hA₁ hB₀ hB₁ Z).functor.IsEquivalence by
    infer_instance

theorem weak {A B : SSet.{u}} (g : A ⟶ B) (r : B ⟶ A)
    (HA : A ⊗ J ⟶ A) (HB : B ⊗ J ⟶ B)
    (hA₀ : intervalEndpoint A false ≫ HA = g ≫ r)
    (hA₁ : intervalEndpoint A true ≫ HA = 𝟙 A)
    (hB₀ : intervalEndpoint B false ≫ HB = r ≫ g)
    (hB₁ : intervalEndpoint B true ≫ HB = 𝟙 B) :
    DaggerNativeJoyalMappingTest.weakCategoricalEquivalences g :=
  fun Z _ ↦ preHoFunctor_isEquivalence g r HA HB hA₀ hA₁ hB₀ hB₁ Z

end
end DaggerNativeWalkingTwoSidedMappingEquivalence
