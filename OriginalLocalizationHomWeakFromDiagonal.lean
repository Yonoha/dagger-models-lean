import OriginalWholeBarFixedBaseComparisonBridge
import OriginalStrictSimplicialPiZeroGroupoid

/-! Remove BOTH fibre-comparison hypotheses from the original localization Hom criterion. -/
set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra DaggerModels
open DaggerOriginalWholeBarFixedBaseComparisonBridge
open DaggerOriginalSimplicialCategoryBarReplacementFibreComparison
open DaggerOriginalStrictSimplicialPiZeroGroupoid DaggerOriginalSimplicialGroupoidCompletion
open DaggerOriginalSimplicialCategoryDiagonalNerve DaggerOriginalAmbientDaggerPiZeroGroupoid
open DaggerOriginalCompletionWeakNecessity
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerOriginalLocalizationHomWeakFromDiagonal
noncomputable section

theorem completion_hasActualComponentGroupoid (C : SimplicialCat.{u, u}) :
    HasActualComponentGroupoid (completion C) :=
  ⟨completedComponentGroupoid C, completedComponentGroupoid_category C⟩

theorem localizationHom_weak_of_diagonal (C : SimplicialCat.{u, u})
    (hC : HasActualComponentGroupoid C) (hnerve : WeakEquivalence (diagonalLocalization C))
    (x y : C.Obj) : WeakEquivalence (localizationHom C x y) :=
  localizationHom_weak_of_diagonal_and_comparisons C x hnerve
    (fixedBaseStrictComparison_weak C hC x)
    (fixedBaseStrictComparison_weak (completion C) (completion_hasActualComponentGroupoid C) x) y

theorem localizationHom_weak_iff_groupoid_given_diagonal (C : SimplicialCat.{u, u})
    (hnerve : WeakEquivalence (diagonalLocalization C)) :
    (∀ x y : C.Obj, WeakEquivalence (localizationHom C x y)) ↔
      HasActualComponentGroupoid C :=
  ⟨localizationWeak_implies_actualPiZeroGroupoid C,
    fun hC x y ↦ localizationHom_weak_of_diagonal C hC hnerve x y⟩

end
end DaggerOriginalLocalizationHomWeakFromDiagonal
