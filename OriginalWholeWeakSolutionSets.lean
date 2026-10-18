import WholeWeakSolutionSets
import OriginalWeakInverseWitnessImage

/-! Both ENTIRE original native and anti-involutive weak classes have exact Smith solution data. -/
set_option autoImplicit false
open CategoryTheory DaggerModels
open DaggerNativeJoyalMappingTest DaggerActualAntiJoyalMappingWeakProperties
open DaggerOriginalWeakInverseWitnessImage
universe u
namespace DaggerOriginalWholeWeakSolutionSets
noncomputable section

def native (I : MorphismProperty SSet.{u}) [MorphismProperty.IsSmall.{u} I] :
    DaggerSmithSolutionSet.SolutionData.{u} I weakCategoricalEquivalences :=
  (DaggerWholeWeakSolutionSets.exists_solutionData
    DaggerNativeInnerHornFactorization.replacement.{u} I weakCategoricalEquivalences
    native_obj_weak (fun f hf ↦ (native_weak_iff_image f).1 hf)).some

def actual (I : MorphismProperty AntiInvolutiveSSet.{u}) [MorphismProperty.IsSmall.{u} I] :
    DaggerSmithSolutionSet.SolutionData.{u} I weakEquivalences :=
  (DaggerWholeWeakSolutionSets.exists_solutionData
    actualUnderlyingReplacement.{u} I weakEquivalences
    actual_obj_weak (fun f hf ↦ (actual_weak_iff_image f).1 hf)).some

end
end DaggerOriginalWholeWeakSolutionSets
