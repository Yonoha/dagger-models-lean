import FiniteSSetIhomAccessibility
import FiniteTensorSourcePresentability

/-! A whole presentable domain gives an accessible internal-Hom functor at the same rank. -/
set_option autoImplicit false
open CategoryTheory Limits Opposite MonoidalCategory Simplicial
universe u
namespace DaggerPresentableParameterIhomAccessibility
noncomputable section

instance accessible (κ : Cardinal.{u}) [Fact κ.IsRegular]
    (K : SSet.{u}) [IsCardinalPresentable K κ] : (ihom K).IsCardinalAccessible κ where
  preservesColimitOfShape J _ _ := by
    apply preservesColimitsOfShape_of_evaluation (ihom K) J
    intro q
    have : IsCardinalPresentable (K ⊗ Δ[q.unop.len]) κ :=
      DaggerFiniteTensorSourcePresentability.tensor_presentable κ K Δ[q.unop.len]
    have : (coyoneda.obj (op (K ⊗ Δ[q.unop.len]))).IsCardinalAccessible κ := inferInstance
    have : (ihom K ⋙ (evaluation SimplexCategoryᵒᵖ (Type u)).obj q).IsCardinalAccessible κ :=
      Functor.isCardinalAccessible_of_natIso
        (DaggerFiniteSSetIhomAccessibility.evaluationIso K q.unop.len).symm κ
    exact Functor.preservesColimitsOfShape_of_isCardinalAccessible _ κ J

end
end DaggerPresentableParameterIhomAccessibility
