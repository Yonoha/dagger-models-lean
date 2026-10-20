import WholeWitnessPresentability
import OriginalSmithCardinalRecovered
import OriginalRLPArrowRecovered
import NativeSSetLocallyPresentable

/-!
# Every whole witness has an individual presentability rank

Uniform presentability is applied to one original arrow and the five entire
simplicial sources used by the inverse and triangle constraints. The resulting
rank may depend on the witness. No common small generator is asserted.
-/
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory Simplicial
open DaggerSimplexInverseWitnessCategory DaggerWholeWitnessSides
universe u v w
namespace DaggerWholeWitnessIndividualRanks
noncomputable section
attribute [local instance] Cardinal.fact_isRegular_aleph0
variable {C : Type w} [Category.{v} C] (R : C ⥤ SSet.{u})

def sources (X : Witness R) : Fin 5 → SSet.{u} :=
  ![R.obj X.arrow.right, side R X false ⊗ Δ[1], side R X false ⊗ Δ[2],
    side R X true ⊗ Δ[1], side R X true ⊗ Δ[2]]

theorem exists_individual_rank [IsLocallyPresentable.{u} C]
    [HasColimitsOfSize.{u, u} C] [R.IsCardinalAccessible Cardinal.aleph0.{u}]
    (X : Witness R) :
    ∃ (κ : Cardinal.{u}) (_ : Fact κ.IsRegular), IsCardinalPresentable X κ := by
  have : IsLocallyPresentable.{u} (Arrow C) := DaggerRLPAccessibility.arrowLocallyPresentable C
  obtain ⟨κA, hκA, hA⟩ := DaggerSmithSolutionSet.uniformPresentability
    (fun _ : ULift.{u} PUnit ↦ X.arrow)
  obtain ⟨κS, hκS, hS⟩ := DaggerSmithSolutionSet.uniformPresentability
    (fun i : ULift.{u} (Fin 5) ↦ sources R X i.down)
  have : Fact κA.IsRegular := ⟨hκA⟩
  have : Fact κS.IsRegular := ⟨hκS⟩
  let κ := max κA κS
  have hκ : κ.IsRegular := by
    rcases le_total κA κS with h | h
    · simpa only [κ, max_eq_right h] using hκS
    · simpa only [κ, max_eq_left h] using hκA
  have : Fact κ.IsRegular := ⟨hκ⟩
  have : IsCardinalPresentable X.arrow κA := hA (ULift.up PUnit.unit)
  have : IsCardinalPresentable X.arrow κ :=
    isCardinalPresentable_of_le X.arrow (le_max_left κA κS)
  have hSources : ∀ i : Fin 5, IsCardinalPresentable (sources R X i) κ := by
    intro i
    have : IsCardinalPresentable (sources R X i) κS := hS (ULift.up i)
    exact isCardinalPresentable_of_le _ (le_max_right κA κS)
  have : IsCardinalPresentable (R.obj X.arrow.right) κ := hSources 0
  have hTensor : ∀ b, IsCardinalPresentable (side R X b ⊗ Δ[1]) κ ∧
      IsCardinalPresentable (side R X b ⊗ Δ[2]) κ := by
    intro b
    cases b
    · exact ⟨hSources 1, hSources 2⟩
    · exact ⟨hSources 3, hSources 4⟩
  have : R.IsCardinalAccessible κ :=
    R.isCardinalAccessible_of_le (κ := Cardinal.aleph0.{u}) hκ.aleph0_le
  exact ⟨κ, inferInstance, DaggerWholeWitnessPresentability.witness_presentable R κ X hTensor⟩

end
end DaggerWholeWitnessIndividualRanks
