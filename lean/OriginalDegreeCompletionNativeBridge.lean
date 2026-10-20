import OriginalDiagonalLocalizationReduction
import NativeGroupoidCompletionNerveBaseCases

/-! Native groupoid completion in each degree agrees with the SAME original completion unit. -/
set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra Simplicial Opposite DaggerModels
open DaggerOriginalSimplicialDegreeCategory DaggerOriginalSimplicialGroupoidCompletion
open DaggerOriginalDiagonalLocalizationReduction DaggerNativeGroupoidCompletionNerveBaseCases
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerOriginalDegreeCompletionNativeBridge
noncomputable section

def degreeCompletionFunctor (C : SimplicialCat.{u, u}) (n : SimplexCategoryᵒᵖ) :
    degreeObjects (completion C) n ⥤ FreeGroupoid (degreeObjects C n) where
  obj := completedObject C n
  map f := f
  map_id _ := rfl
  map_comp _ _ := rfl

def degreeCompletionFullyFaithful (C : SimplicialCat.{u, u}) (n : SimplexCategoryᵒᵖ) :
    (degreeCompletionFunctor C n).FullyFaithful where
  preimage f := f
  map_preimage _ := rfl
  preimage_map _ := rfl

instance degreeCompletion_isEquivalence (C : SimplicialCat.{u, u})
    (n : SimplexCategoryᵒᵖ) : (degreeCompletionFunctor C n).IsEquivalence := by
  have := (degreeCompletionFullyFaithful C n).full
  have := (degreeCompletionFullyFaithful C n).faithful
  have : (degreeCompletionFunctor C n).EssSurj := by
    constructor
    intro y
    obtain ⟨x, hx⟩ := (FreeGroupoid.of_obj_bijective (C := degreeObjects C n)).surjective y
    exact ⟨x, ⟨eqToIso hx⟩⟩
  exact {}

theorem localization_degree_square (C : SimplicialCat.{u, u}) (n : SimplexCategoryᵒᵖ) :
    degreeFunctor (localization C) n ⋙ degreeCompletionFunctor C n =
      FreeGroupoid.of (degreeObjects C n) := rfl

theorem localization_degree_nerve_square (C : SimplicialCat.{u, u})
    (n : SimplexCategoryᵒᵖ) :
    nerveMap (degreeFunctor (localization C) n) ≫ nerveMap (degreeCompletionFunctor C n) =
      nerveMap (FreeGroupoid.of (degreeObjects C n)) := by
  change nerveMap (degreeFunctor (localization C) n ⋙ degreeCompletionFunctor C n) = _
  rw [localization_degree_square]

theorem degree_localization_weak_of_native_unit (C : SimplicialCat.{u, u})
    (n : SimplexCategoryᵒᵖ) (hn : WeakEquivalence
      (nerveMap (FreeGroupoid.of (degreeObjects C n)))) :
    WeakEquivalence (nerveMap (degreeFunctor (localization C) n)) := by
  have := hn
  have := nerveMap_weak_of_equivalence (degreeCompletionFunctor C n)
  exact weakEquivalence_of_postcomp_of_fac (localization_degree_nerve_square C n)

theorem diagonalLocalization_weak_of_native_units (C : SimplicialCat.{u, u})
    (hC : ∀ n, WeakEquivalence (nerveMap (FreeGroupoid.of (degreeObjects C n)))) :
    WeakEquivalence (DaggerOriginalSimplicialCategoryDiagonalNerve.diagonalLocalization C) :=
  diagonalLocalization_weak_of_degree_nerve C (fun n ↦ degree_localization_weak_of_native_unit C n
    (hC n))

end
end DaggerOriginalDegreeCompletionNativeBridge
