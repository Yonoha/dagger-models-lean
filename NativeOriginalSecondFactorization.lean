import NativeOriginalWeakMonoTransfinite
import FullOriginalSecondFactorizationAssembly

/-! Unconditional second factorization for the entire original ordinary Joyal classes. -/
set_option autoImplicit false
open CategoryTheory
open DaggerNativeJoyalMappingTest DaggerNativeJoyalFirstFactorization
universe u
namespace DaggerNativeOriginalSecondFactorization
noncomputable section

def secondFactorization : MorphismProperty.FunctorialFactorizationData
    (MorphismProperty.monomorphisms SSet.{u} ⊓ weakCategoricalEquivalences)
    candidateFibrations.{u} :=
  DaggerFullOriginalSecondFactorizationAssembly.native

instance hasSecondFactorization :
    MorphismProperty.HasFunctorialFactorization
      (MorphismProperty.monomorphisms SSet.{u} ⊓ weakCategoricalEquivalences)
      candidateFibrations.{u} := ⟨⟨secondFactorization⟩⟩

end
end DaggerNativeOriginalSecondFactorization
