import WholeWitnessCommonRankFamilies

/-! One rank retains the original local presentations and the bounded whole witness family. -/
set_option autoImplicit false
open CategoryTheory Limits
open DaggerSimplexInverseWitnessCategory
universe u v w
namespace DaggerWholeSolutionStrongCommonRanks
noncomputable section
attribute [local instance] Cardinal.fact_isRegular_aleph0

theorem exists_rank {C : Type w} [Category.{v} C] [HasPullbacks C] [HasTerminal C]
    [IsLocallyFinitelyPresentable.{u} C] (R : C ⥤ SSet.{u})
    [R.IsCardinalAccessible Cardinal.aleph0.{u}] (A : Type u) (I : A → Arrow C) :
    ∃ (κ : Cardinal.{u}) (_ : Fact κ.IsRegular), Cardinal.aleph0 < κ ∧
      IsCardinalLocallyPresentable.{u} C κ ∧
      IsCardinalLocallyPresentable.{u} (Arrow C) κ ∧
      (∀ a, IsCardinalPresentable (I a) κ) ∧ R.IsCardinalAccessible κ ∧
      (∀ X : C, IsCardinalPresentable X κ → IsCardinalPresentable (R.obj X) κ) ∧
      ∃ (K : Type u) (G : K → Witness R),
        (∀ k, IsCardinalPresentable (G k).arrow κ) ∧
        (∀ X : Witness R, IsCardinalPresentable X.arrow κ → ∃ k, Nonempty (X ≅ G k)) := by
  have : IsLocallyPresentable.{u} C :=
    ⟨Cardinal.aleph0.{u}, inferInstance, inferInstance⟩
  have : IsLocallyPresentable.{u} (Arrow C) := DaggerRLPAccessibility.arrowLocallyPresentable C
  obtain ⟨μ, hμ, hI⟩ := DaggerSmithSolutionSet.uniformPresentability I
  have : Fact μ.IsRegular := ⟨hμ⟩
  obtain ⟨κ, hκ, hμκ, hC, _, hR, hStrong⟩ :=
    DaggerWholeReplacementPrescribedStrongRanks.exists_above R μ
  have : Fact κ.IsRegular := hκ
  have : IsCardinalLocallyPresentable.{u} C κ := hC
  have : R.IsCardinalAccessible κ := hR
  have : IsCardinalLocallyPresentable.{u} (Arrow C) κ :=
    DaggerArrowCardinalLocalPresentability.atRank C κ
  obtain ⟨K, G, _, _, hG, hcover⟩ :=
    DaggerWholeWitnessBoundedBaseFamilies.bounded_family R κ
  refine ⟨κ, inferInstance, lt_of_le_of_lt hμ.aleph0_le hμκ, hC, inferInstance,
    ?_, hR, hStrong, K, G, (fun k ↦ (hG k).1), hcover⟩
  intro a
  have : IsCardinalPresentable (I a) μ := hI a
  exact isCardinalPresentable_of_le _ hμκ.le

end
end DaggerWholeSolutionStrongCommonRanks
