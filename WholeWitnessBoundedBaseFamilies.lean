import WholeWitnessEssentiallySmallBaseProperties
import WholeWitnessSmallFamilyRanks

/-!
# Constructing a small family of all complete witnesses with presentable base arrows

The family includes every choice of inverse and triangle data, up to actual
whole-witness isomorphism. It covers the stated base rank, not all large witnesses.
No cardinal-filtered presentation by this family is asserted.
-/
set_option autoImplicit false
open CategoryTheory Limits
open DaggerSimplexInverseWitnessCategory
universe u v w
namespace DaggerWholeWitnessBoundedBaseFamilies
noncomputable section
attribute [local instance] Cardinal.fact_isRegular_aleph0
variable {C : Type w} [Category.{v} C] [IsLocallyPresentable.{u} C]
    [HasColimitsOfSize.{u, u} C] (R : C ⥤ SSet.{u})
    [R.IsCardinalAccessible Cardinal.aleph0.{u}]

theorem bounded_family (κ : Cardinal.{u}) [Fact κ.IsRegular]
    [IsCardinalAccessibleCategory.{u} (Arrow C) κ] :
    ∃ (K : Type u) (G : K → Witness R) (ν : Cardinal.{u}) (_ : Fact ν.IsRegular),
      (∀ k, IsCardinalPresentable (G k).arrow κ ∧ IsCardinalPresentable (G k) ν) ∧
      (∀ X : Witness R, IsCardinalPresentable X.arrow κ → ∃ k, Nonempty (X ≅ G k)) := by
  let P := (isCardinalPresentable (Arrow C) κ).inverseImage (forget R)
  have : ObjectProperty.EssentiallySmall.{u} P :=
    DaggerWholeWitnessEssentiallySmallBaseProperties.inverseImageEssentiallySmall
      R (isCardinalPresentable (Arrow C) κ)
  obtain ⟨Q, hQ, hQP, hPQ⟩ := ObjectProperty.EssentiallySmall.exists_small_le.{u} P
  have : ObjectProperty.Small.{u} Q := hQ
  let K := Shrink (Subtype Q)
  let G : K → Witness R := fun k ↦ ((equivShrink (Subtype Q)).symm k).val
  obtain ⟨ν, hν, hG⟩ := DaggerWholeWitnessSmallFamilyRanks.exists_small_family_rank R G
  refine ⟨K, G, ν, hν, fun k ↦ ⟨?_, hG k⟩, ?_⟩
  · exact hQP _ ((equivShrink (Subtype Q)).symm k).property
  · intro X hX
    obtain ⟨Y, hY, ⟨e⟩⟩ := hPQ X hX
    refine ⟨equivShrink (Subtype Q) ⟨Y, hY⟩, ⟨?_⟩⟩
    simpa only [G, Equiv.symm_apply_apply] using e

theorem exists_bounded_family :
    ∃ (κ : Cardinal.{u}) (_ : Fact κ.IsRegular)
      (K : Type u) (G : K → Witness R) (ν : Cardinal.{u}) (_ : Fact ν.IsRegular),
      (∀ k, IsCardinalPresentable (G k).arrow κ ∧ IsCardinalPresentable (G k) ν) ∧
      (∀ X : Witness R, IsCardinalPresentable X.arrow κ → ∃ k, Nonempty (X ≅ G k)) := by
  have : IsLocallyPresentable.{u} (Arrow C) := DaggerRLPAccessibility.arrowLocallyPresentable C
  obtain ⟨κ, hκ, hC⟩ := IsLocallyPresentable.exists_cardinal (Arrow C)
  have : Fact κ.IsRegular := hκ
  have : IsCardinalLocallyPresentable (Arrow C) κ := hC
  obtain ⟨K, G, ν, hν, hG, hcover⟩ := bounded_family R κ
  exact ⟨κ, inferInstance, K, G, ν, hν, hG, hcover⟩

end
end DaggerWholeWitnessBoundedBaseFamilies
