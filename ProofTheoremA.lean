import ChallengeTheoremA
import OriginalGlobalModelDataRecovered
import OriginalGlobalLeftProperRecovered

set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra DaggerModels
open scoped SSet.modelCategoryQuillen
universe u

namespace DaggerTheoremAProof

private noncomputable abbrev M : ModelCategory DaggerTheoremAChallenge.G.{u} :=
  DaggerGlobalModel.standardModelCategory.{u}

private theorem weak_bridge :
    DaggerTheoremAChallenge.W.{u} =
      DaggerGlobalDK.daggerDK DaggerUnitaryInvariance.standardReplacement.{u} := by
  rfl

private theorem finite_generation :
    DaggerActualGlobalModelChallenge.finiteGenerationStatement.{u} := by
  let d := DaggerGlobalModel.standardCombinatorialData.{u}
  exact ⟨d.locallyFinitelyPresentable, d.smallI, d.smallJ,
    (fun f hf ↦ d.domainsI f hf), (fun f hf ↦ d.domainsJ f hf)⟩

private theorem classes : DaggerTheoremAChallenge.classes M.{u} := by
  letI : ModelCategory DaggerTheoremAChallenge.G.{u} := M.{u}
  refine ⟨?_, ?_, ?_⟩
  · change weakEquivalences DaggerTheoremAChallenge.G.{u} =
      DaggerTheoremAChallenge.W.{u}
    rw [weak_bridge]
    exact DaggerGlobalModel.weakEquivalences_eq DaggerUnitaryInvariance.standardReplacement
  · change cofibrations DaggerTheoremAChallenge.G.{u} =
      DaggerTheoremAChallenge.I.{u}.rlp.llp
    exact DaggerGlobalModel.cofibrations_eq
  · change fibrations DaggerTheoremAChallenge.G.{u} =
      DaggerTheoremAChallenge.J.{u}.rlp
    exact DaggerGlobalModel.fibrations_eq

private theorem trivial_fibrations :
    DaggerTheoremAChallenge.trivialFibrations M.{u} := by
  intro C D p
  exact DaggerGlobalModel.trivialFibration_iff_original
    DaggerUnitaryInvariance.standardReplacement p

private theorem left_proper : DaggerTheoremAChallenge.leftProper.{u} := by
  intro C C' B B' f i j f' sq hi hf
  rw [weak_bridge] at hf ⊢
  exact DaggerGlobalLeftProper.standard_leftProper sq hi hf

theorem verified : DaggerTheoremAChallenge.statement.{u} :=
  ⟨M.{u}, classes, finite_generation, trivial_fibrations, left_proper⟩

end DaggerTheoremAProof
