import TopObjectPropertyEquivalence
import OriginalN0SharpGeneratorsRecovered
import OriginalN0CommonCardinalsRecovered
import OriginalQuasiReplacementsAccessible
import NativeSSetLocallyPresentable
import ActualAntiInvolutivePresentable

/-!
# Actual common strong-accessibility ranks for both entire original replacements

Reuse the proved sharp-rank construction with the full target property. All
presentable source objects at the resulting rank have presentable images at
that same rank. No weak witness presentation is inferred from this result.
-/
set_option autoImplicit false
open CategoryTheory
open DaggerAccessibleInverseImage
universe u v w
namespace DaggerWholeReplacementStrongRanks
noncomputable section
attribute [local instance] Cardinal.fact_isRegular_aleph0

theorem exists_strong_rank {C : Type w} [Category.{v} C]
    [IsLocallyFinitelyPresentable.{u} C] (R : C ⥤ SSet.{u})
    [R.IsCardinalAccessible Cardinal.aleph0.{u}] :
    ∃ (κ : Cardinal.{u}) (_ : Fact κ.IsRegular), Cardinal.aleph0 < κ ∧
      IsCardinalLocallyPresentable C κ ∧ IsCardinalLocallyPresentable SSet.{u} κ ∧
      R.IsCardinalAccessible κ ∧
      (∀ X : C, IsCardinalPresentable X κ → IsCardinalPresentable (R.obj X) κ) := by
  let P : ObjectProperty SSet.{u} := ⊤
  have : IsCardinalAccessibleCategory.{u} P.FullSubcategory Cardinal.aleph0.{u} :=
    DaggerTopObjectPropertyEquivalence.accessible SSet.{u} Cardinal.aleph0.{u}
  have : P.ι.IsCardinalAccessible Cardinal.aleph0.{u} :=
    DaggerTopObjectPropertyEquivalence.inclusion_accessible SSet.{u} Cardinal.aleph0.{u}
  obtain ⟨θ, hC, hD, _, hR, _, hStrong, _⟩ :=
    exists_common_strong_regular Cardinal.aleph0.{u} R P
  let κ := sharpRegular (Order.succ Cardinal.aleph0.{u}) θ
  have : Fact κ.IsRegular := ⟨sharpRegular_isRegular _ _⟩
  refine ⟨κ, inferInstance, ?_, hC, hD, hR, hStrong⟩
  exact (Order.lt_succ Cardinal.aleph0.{u}).trans (left_lt_sharpRegular _ _)

end
end DaggerWholeReplacementStrongRanks
