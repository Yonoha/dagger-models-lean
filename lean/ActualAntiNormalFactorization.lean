import ActualAntiInvolutivePresentable
import ActualAntiNormalBoundaryLifting
import OriginalSmithCardinalRecovered

/-!
# A functorial weak factorization system for the full original normal class

The original normal generator recognition theorem is combined with the
existing general Smith cardinal witness and native small-object argument.
No Joyal model structure, DCH model structure, or caller-supplied factorization is used.
-/
set_option autoImplicit false
open CategoryTheory Limits DaggerModels
open DaggerModels.OriginalAntiInvolutiveNormalMonoSaturation
open DaggerModels.OriginalAntiInvolutiveNormalGeneratorRecognition
universe u
namespace DaggerActualAntiNormalFactorization
noncomputable section

instance generatorsSmall : MorphismProperty.IsSmall.{u} normalGeneratingCofibrations.{u} :=
  MorphismProperty.isSmall_ofHoms _

/-- Uniform presentability data for the literal original free-boundary family. -/
def generatorsCardinal : DaggerSmithSolutionSet.CardinalWitness.{u} normalGeneratingCofibrations.{u} :=
  DaggerSmithSolutionSet.cardinalWitness.{u} _

/-- The entire all-degree normal class is exactly the corresponding left lifting class. -/
theorem normalMonos_eq_generators_rlp_llp :
    normalMonos.{u} = normalGeneratingCofibrations.{u}.rlp.llp := by
  let w := generatorsCardinal.{u}
  letI : Fact w.κ.IsRegular := ⟨w.regular⟩
  letI : OrderBot w.κ.ord.ToType := w.orderBot
  letI : normalGeneratingCofibrations.IsCardinalForSmallObjectArgument w.κ := w.suitable
  rw [SmallObject.llp_rlp_of_isCardinalForSmallObjectArgument normalGeneratingCofibrations w.κ]
  exact normalMonos_eq_normalGeneratorSaturation

/-- Every original morphism admits the actual functorial normal/right-lifting factorization. -/
def normalFactorization :
    normalMonos.{u}.FunctorialFactorizationData normalMonos.{u}.rlp := by
  simpa only [DaggerActualAntiNormalBoundaryLifting.normalMonos_rlp_eq_generators_rlp,
    normalMonos_eq_generators_rlp_llp, MorphismProperty.rlp_llp_rlp] using
    DaggerSmithSolutionSet.soaFactorization.{u} normalGeneratingCofibrations.{u}

instance normalHasFunctorialFactorization :
    normalMonos.{u}.HasFunctorialFactorization normalMonos.{u}.rlp :=
  ⟨⟨normalFactorization⟩⟩

/-- The full left lifting class against all normal-right maps is the original normal class. -/
theorem normalMonos_eq_rlp_llp : normalMonos.{u} = normalMonos.{u}.rlp.llp := by
  rw [DaggerActualAntiNormalBoundaryLifting.normalMonos_rlp_eq_generators_rlp]
  exact normalMonos_eq_generators_rlp_llp

end
end DaggerActualAntiNormalFactorization
