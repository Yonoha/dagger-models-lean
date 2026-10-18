import OriginalCofibrantDegreeFreeRetract
import OriginalDegreewiseCompletionCriterion

/-! The remaining native free-category unit theorem implies the original cofibrant criterion. -/
set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra Opposite DaggerModels
open DaggerOriginalFixedObjectSimplicialCategories DaggerOriginalSimplicialDegreeCategory
open DaggerOriginalCofibrantDegreeFreeRetract DaggerOriginalDegreewiseCompletionCriterion
open DaggerOriginalSimplicialCategoryDiagonalNerve DaggerOriginalSimplicialGroupoidCompletion
open DaggerOriginalAmbientDaggerPiZeroGroupoid
open scoped SSet.modelCategoryQuillen DaggerOriginalAmbientDaggerForgetCofibrancy
universe u
namespace DaggerOriginalCofibrantFreeUnitReduction
noncomputable section

theorem degreeRetractData_of_free_units {O : Type u} (C : FixedSimplicialCategory O)
    [IsCofibrant C]
    (hfree : ∀ n, WeakEquivalence
      (nerveMap (FreeGroupoid.of (Paths (degreeObjects (original O C) n))))) :
    DegreeRetractData (original O C) := by
  intro n
  refine ⟨Cat.of (Paths (degreeObjects (original O C) n)),
    (degreeSection C n).toCatHom, (pathComposition _).toCatHom, ?_, hfree n⟩
  exact congrArg CategoryTheory.Functor.toCatHom (degreeSection_retract C n)

theorem diagonalLocalization_weak_of_free_units {O : Type u} (C : FixedSimplicialCategory O)
    [IsCofibrant C]
    (hfree : ∀ n, WeakEquivalence
      (nerveMap (FreeGroupoid.of (Paths (degreeObjects (original O C) n))))) :
    WeakEquivalence (diagonalLocalization (original O C)) :=
  diagonalLocalization_weak_of_degree_retract_data _ (degreeRetractData_of_free_units C hfree)

theorem localizationHom_weak_of_free_units {O : Type u} (C : FixedSimplicialCategory O)
    [IsCofibrant C] (hC : HasActualComponentGroupoid (original O C))
    (hfree : ∀ n, WeakEquivalence
      (nerveMap (FreeGroupoid.of (Paths (degreeObjects (original O C) n))))) (x y : O) :
    WeakEquivalence (localizationHom (original O C) x y) :=
  localizationHom_weak_of_degree_retract_data _ hC (degreeRetractData_of_free_units C hfree) x y

end
end DaggerOriginalCofibrantFreeUnitReduction
