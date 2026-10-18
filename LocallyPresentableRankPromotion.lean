import NativeSSetLocallyPresentable

/-! Cocompleteness allows promotion to every larger regular local-presentability rank. -/
set_option autoImplicit false
open CategoryTheory Limits
universe u v w
namespace DaggerLocallyPresentableRankPromotion

theorem locallyPresentable_of_le (C : Type w) [Category.{v} C] [HasPullbacks C]
    (κ₀ κ : Cardinal.{u}) [Fact κ₀.IsRegular] [Fact κ.IsRegular]
    [IsCardinalLocallyPresentable.{u} C κ₀] (hle : κ₀ ≤ κ) :
    IsCardinalLocallyPresentable.{u} C κ := by
  obtain ⟨P, hP, hStrong, hPresent⟩ :=
    (IsCardinalLocallyPresentable.iff_exists_isStrongGenerator C κ₀).1 inferInstance
  have : ObjectProperty.Small.{u} P := hP
  apply (IsCardinalLocallyPresentable.iff_exists_isStrongGenerator C κ).2
  refine ⟨P, inferInstance, hStrong, ?_⟩
  intro X hX
  have : IsCardinalPresentable X κ₀ := hPresent X hX
  exact isCardinalPresentable_of_le X hle

end DaggerLocallyPresentableRankPromotion
