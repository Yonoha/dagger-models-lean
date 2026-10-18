import WholeReplacementStrongRanks
import LocallyPresentableRankPromotion

/-! A strong rank for the actual entire replacement above any prescribed regular rank. -/
set_option autoImplicit false
open CategoryTheory Limits DaggerAccessibleInverseImage
universe u v w
namespace DaggerWholeReplacementPrescribedStrongRanks
noncomputable section
attribute [local instance] Cardinal.fact_isRegular_aleph0

theorem exists_above {C : Type w} [Category.{v} C] [HasPullbacks C]
    [IsLocallyFinitelyPresentable.{u} C] (R : C ⥤ SSet.{u})
    [R.IsCardinalAccessible Cardinal.aleph0.{u}]
    (μ : Cardinal.{u}) [hμ : Fact μ.IsRegular] :
    ∃ (κ : Cardinal.{u}) (_ : Fact κ.IsRegular), μ < κ ∧
      IsCardinalLocallyPresentable C κ ∧ IsCardinalLocallyPresentable SSet.{u} κ ∧
      R.IsCardinalAccessible κ ∧
      (∀ X : C, IsCardinalPresentable X κ → IsCardinalPresentable (R.obj X) κ) := by
  have : IsCardinalLocallyPresentable.{u} C μ :=
    DaggerLocallyPresentableRankPromotion.locallyPresentable_of_le C
      Cardinal.aleph0.{u} μ hμ.out.aleph0_le
  have : IsCardinalLocallyPresentable.{u} SSet.{u} μ :=
    DaggerLocallyPresentableRankPromotion.locallyPresentable_of_le SSet.{u}
      Cardinal.aleph0.{u} μ hμ.out.aleph0_le
  have : R.IsCardinalAccessible μ :=
    R.isCardinalAccessible_of_le (κ := Cardinal.aleph0.{u}) hμ.out.aleph0_le
  let P : ObjectProperty SSet.{u} := ⊤
  have : IsCardinalAccessibleCategory.{u} P.FullSubcategory μ :=
    DaggerTopObjectPropertyEquivalence.accessible SSet.{u} μ
  have : P.ι.IsCardinalAccessible μ :=
    DaggerTopObjectPropertyEquivalence.inclusion_accessible SSet.{u} μ
  obtain ⟨θ, hC, hD, _, hR, _, hStrong, _⟩ := exists_common_strong_regular μ R P
  let κ := sharpRegular (Order.succ μ) θ
  have : Fact κ.IsRegular := ⟨sharpRegular_isRegular _ _⟩
  exact ⟨κ, inferInstance, (Order.lt_succ μ).trans (left_lt_sharpRegular _ _),
    hC, hD, hR, hStrong⟩

end
end DaggerWholeReplacementPrescribedStrongRanks
