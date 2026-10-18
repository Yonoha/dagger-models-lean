import OriginalWholeWeakSolutionSets
import ActualAntiNormalFactorization

/-! Exact solution data for the literal original all-degree normal generating family. -/
set_option autoImplicit false
open CategoryTheory DaggerModels
open DaggerModels.OriginalAntiInvolutiveNormalMonoSaturation
open DaggerActualAntiJoyalMappingWeakProperties
universe u
namespace DaggerOriginalNormalGeneratorWholeSolutions
noncomputable section

def actual : DaggerSmithSolutionSet.SolutionData.{u}
    normalGeneratingCofibrations.{u} weakEquivalences.{u} :=
  DaggerOriginalWholeWeakSolutionSets.actual normalGeneratingCofibrations

end
end DaggerOriginalNormalGeneratorWholeSolutions
