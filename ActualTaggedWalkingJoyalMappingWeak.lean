import NativeJoyalMappingTest
import ActualTaggedWalkingMappingEquivalence

set_option autoImplicit false
open CategoryTheory DaggerModels
open DaggerActualTaggedWalkingIsoImageDKObstruction
universe u
namespace DaggerActualTaggedWalkingJoyalMappingWeak

/-- The entire unchanged original underlying tagged map satisfies Joyal's mapping test. -/
theorem taggedGenerator_weakCategoricalEquivalence :
    DaggerNativeJoyalMappingTest.weakCategoricalEquivalences taggedGenerator.{u}.hom :=
  fun Z _ ↦ DaggerActualTaggedWalkingMappingEquivalence.tagged_pre_isEquivalence Z

end DaggerActualTaggedWalkingJoyalMappingWeak
