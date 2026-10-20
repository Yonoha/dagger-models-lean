import WholeWitnessIndividualRanks

/-!
# One actual rank works for any given small family of complete witnesses

The family is supplied, not constructed here. This does not prove that it
presents or generates every witness in the entire category.
-/
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory Simplicial
open DaggerSimplexInverseWitnessCategory DaggerWholeWitnessSides
open DaggerWholeWitnessIndividualRanks
universe u v w
namespace DaggerWholeWitnessSmallFamilyRanks
noncomputable section
attribute [local instance] Cardinal.fact_isRegular_aleph0
variable {C : Type w} [Category.{v} C] (R : C ⥤ SSet.{u})

theorem exists_small_family_rank [IsLocallyPresentable.{u} C]
    [HasColimitsOfSize.{u, u} C] [R.IsCardinalAccessible Cardinal.aleph0.{u}]
    {K : Type u} (G : K → Witness R) :
    ∃ (κ : Cardinal.{u}) (_ : Fact κ.IsRegular), ∀ k, IsCardinalPresentable (G k) κ := by
  have : IsLocallyPresentable.{u} (Arrow C) := DaggerRLPAccessibility.arrowLocallyPresentable C
  obtain ⟨κA, hκA, hA⟩ := DaggerSmithSolutionSet.uniformPresentability
    (fun k : K ↦ (G k).arrow)
  obtain ⟨κS, hκS, hS⟩ := DaggerSmithSolutionSet.uniformPresentability
    (fun i : K × Fin 5 ↦ sources R (G i.1) i.2)
  have : Fact κA.IsRegular := ⟨hκA⟩
  have : Fact κS.IsRegular := ⟨hκS⟩
  let κ := max κA κS
  have hκ : κ.IsRegular := by
    rcases le_total κA κS with h | h
    · simpa only [κ, max_eq_right h] using hκS
    · simpa only [κ, max_eq_left h] using hκA
  have : Fact κ.IsRegular := ⟨hκ⟩
  refine ⟨κ, inferInstance, fun k ↦ ?_⟩
  have : IsCardinalPresentable (G k).arrow κA := hA k
  have : IsCardinalPresentable (G k).arrow κ :=
    isCardinalPresentable_of_le (G k).arrow (le_max_left κA κS)
  have hSources : ∀ i : Fin 5, IsCardinalPresentable (sources R (G k) i) κ := by
    intro i
    have : IsCardinalPresentable (sources R (G k) i) κS := hS (k, i)
    exact isCardinalPresentable_of_le _ (le_max_right κA κS)
  have : IsCardinalPresentable (R.obj (G k).arrow.right) κ := hSources 0
  have hTensor : ∀ b, IsCardinalPresentable (side R (G k) b ⊗ Δ[1]) κ ∧
      IsCardinalPresentable (side R (G k) b ⊗ Δ[2]) κ := by
    intro b
    cases b
    · exact ⟨hSources 1, hSources 2⟩
    · exact ⟨hSources 3, hSources 4⟩
  have : R.IsCardinalAccessible κ :=
    R.isCardinalAccessible_of_le (κ := Cardinal.aleph0.{u}) hκ.aleph0_le
  exact DaggerWholeWitnessPresentability.witness_presentable R κ (G k) hTensor

end
end DaggerWholeWitnessSmallFamilyRanks
