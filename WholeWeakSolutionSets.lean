import WholeWitnessBoundedSolutionData

/-! The entire original weak class admits the exact Smith solution set unconditionally. -/
set_option autoImplicit false
open CategoryTheory Limits
open DaggerSimplexInverseWitnessCategory
universe u v w
namespace DaggerWholeWeakSolutionSets
noncomputable section
attribute [local instance] Cardinal.fact_isRegular_aleph0

theorem exists_solutionData {C : Type w} [Category.{v} C] [HasPullbacks C] [HasTerminal C]
    [IsLocallyFinitelyPresentable.{u} C] (R : C ⥤ SSet.{u})
    [R.IsCardinalAccessible Cardinal.aleph0.{u}] (I W : MorphismProperty C)
    [MorphismProperty.IsSmall.{u} I]
    (hweak : ∀ X : Witness R, W X.arrow.hom)
    (hcover : ∀ f : Arrow C, W f.hom → ∃ X : Witness R, X.arrow = f) :
    Nonempty (DaggerSmithSolutionSet.SolutionData.{u} I W) := by
  obtain ⟨κ, hκ, hω, hC, hArrow, hI, hR, hStrong, K, G, _, hG⟩ :=
    DaggerWholeSolutionStrongCommonRanks.exists_rank R (Shrink I.toSet)
      (fun i ↦ ((equivShrink I.toSet).symm i).val)
  have : Fact κ.IsRegular := hκ
  have : IsCardinalLocallyPresentable.{u} C κ := hC
  have : IsCardinalLocallyPresentable.{u} (Arrow C) κ := hArrow
  have : R.IsCardinalAccessible κ := hR
  have hI' : ∀ i : I.toSet, IsCardinalPresentable i.val κ := by
    intro i
    simpa only [Equiv.symm_apply_apply] using hI (equivShrink I.toSet i)
  exact ⟨DaggerWholeWitnessBoundedSolutionData.atRank R κ hω hStrong I W K G hG
    hweak hcover hI'⟩

end
end DaggerWholeWeakSolutionSets
