import WholeWitnessPresentability
import ArrowEndpointPresentability
import FiniteTensorSourcePresentability

/-! Presentable original base arrows yield whole witnesses at that very same rank. -/
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory Simplicial
open DaggerSimplexInverseWitnessCategory DaggerWholeWitnessSides
universe u v w
namespace DaggerWholeWitnessSameRankPresentability

variable {C : Type w} [Category.{v} C] [HasTerminal C] [HasColimitsOfSize.{u, u} C]
    (R : C ⥤ SSet.{u}) (κ : Cardinal.{u}) [Fact κ.IsRegular] [R.IsCardinalAccessible κ]

theorem same_rank (hR : ∀ A : C, IsCardinalPresentable A κ →
    IsCardinalPresentable (R.obj A) κ) (X : Witness R) [IsCardinalPresentable X.arrow κ] :
    IsCardinalPresentable X κ := by
  have : IsCardinalPresentable X.arrow.left κ :=
    DaggerArrowEndpointPresentability.left_presentable C κ X.arrow
  have : IsCardinalPresentable X.arrow.right κ :=
    DaggerArrowEndpointPresentability.right_presentable C κ X.arrow
  have : IsCardinalPresentable (R.obj X.arrow.left) κ := hR _ inferInstance
  have : IsCardinalPresentable (R.obj X.arrow.right) κ := hR _ inferInstance
  have : IsCardinalPresentable (side R X false) κ := by
    change IsCardinalPresentable (R.obj X.arrow.left) κ
    infer_instance
  have : IsCardinalPresentable (side R X true) κ := by
    change IsCardinalPresentable (R.obj X.arrow.right) κ
    infer_instance
  have ht : ∀ b, IsCardinalPresentable (side R X b ⊗ Δ[1]) κ ∧
      IsCardinalPresentable (side R X b ⊗ Δ[2]) κ := by
    intro b
    cases b
    · exact ⟨DaggerFiniteTensorSourcePresentability.tensor_presentable κ _ _,
        DaggerFiniteTensorSourcePresentability.tensor_presentable κ _ _⟩
    · exact ⟨DaggerFiniteTensorSourcePresentability.tensor_presentable κ _ _,
        DaggerFiniteTensorSourcePresentability.tensor_presentable κ _ _⟩
  exact DaggerWholeWitnessPresentability.witness_presentable R κ X ht

end DaggerWholeWitnessSameRankPresentability
