import BoundedWitnessPresentationFactorization
import OriginalArrowFilteredPresentations

/-! Every original whole witness receives a bounded whole witness through any presentable square. -/
set_option autoImplicit false
open CategoryTheory Limits
open DaggerSimplexInverseWitnessCategory
universe u v w
namespace DaggerBoundedWholeWitnessFactorization
noncomputable section
attribute [local instance] Cardinal.fact_isRegular_aleph0
variable {C : Type w} [Category.{v} C] [HasTerminal C] [HasColimitsOfSize.{u, u} C]
  (R : C ⥤ SSet.{u}) [R.IsCardinalAccessible Cardinal.aleph0.{u}]
  (κ : Cardinal.{u}) [Fact κ.IsRegular] [R.IsCardinalAccessible κ]
  [IsCardinalLocallyPresentable.{u} (Arrow C) κ]
  (hω : Cardinal.aleph0 < κ)
  (hR : ∀ X : C, IsCardinalPresentable X κ → IsCardinalPresentable (R.obj X) κ)

include hω hR

theorem factor (X : Witness R) (A : Arrow C) [IsCardinalPresentable A κ] (φ : A ⟶ X.arrow) :
    ∃ Y : Witness R, IsCardinalPresentable Y.arrow κ ∧
      ∃ (a : A ⟶ Y.arrow) (b : Y ⟶ X), a ≫ b.square = φ := by
  obtain ⟨J, _, _, F, ι, ⟨hc⟩, hF⟩ :=
    DaggerOriginalArrowFilteredPresentations.exists_presentation κ X.arrow
  exact DaggerBoundedWitnessPresentationFactorization.factor R κ hω hR
    (Cocone.mk X.arrow ι) hc X.data hF A φ

end
end DaggerBoundedWholeWitnessFactorization
