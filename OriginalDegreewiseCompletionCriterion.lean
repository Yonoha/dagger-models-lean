import OriginalDegreeCompletionNativeBridge
import NativeCategoryCompletionNerveRetracts

/-! Exact degreewise native retract data feed the original diagonal and localization criteria. -/
set_option autoImplicit false
open CategoryTheory Limits HomotopicalAlgebra Simplicial Opposite DaggerModels
open DaggerOriginalSimplicialDegreeCategory DaggerOriginalDegreeCompletionNativeBridge
open DaggerOriginalSimplicialCategoryDiagonalNerve DaggerOriginalSimplicialGroupoidCompletion
open DaggerOriginalSimplicialGroupoidCompletionUniversal
open DaggerOriginalLocalizationHomWeakFromDiagonal DaggerOriginalAmbientDaggerPiZeroGroupoid
open DaggerNativeGroupoidCompletionNerveBaseCases
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerOriginalDegreewiseCompletionCriterion
noncomputable section

def DegreeRetractData (C : SimplicialCat.{u, u}) : Prop :=
  ∀ n, ∃ (D : Cat.{u, u}) (i : Cat.of (degreeObjects C n) ⟶ D)
    (r : D ⟶ Cat.of (degreeObjects C n)), i ≫ r = 𝟙 _ ∧
      WeakEquivalence (nerveMap (FreeGroupoid.of D))

theorem diagonalLocalization_weak_of_degree_retract_data (C : SimplicialCat.{u, u})
    (hC : DegreeRetractData C) : WeakEquivalence (diagonalLocalization C) := by
  apply diagonalLocalization_weak_of_native_units C
  intro n
  obtain ⟨D, i, r, hi, hD⟩ := hC n
  exact DaggerNativeCategoryCompletionNerveRetracts.unit_weak_of_retract i r hi hD

theorem localizationHom_weak_of_degree_retract_data (C : SimplicialCat.{u, u})
    (hC : HasActualComponentGroupoid C) (hD : DegreeRetractData C) (x y : C.Obj) :
    WeakEquivalence (localizationHom C x y) :=
  localizationHom_weak_of_diagonal C hC (diagonalLocalization_weak_of_degree_retract_data C hD)
    x y

theorem diagonalLocalization_weak_of_initial_degrees (C : SimplicialCat.{u, u})
    (hC : ∀ n, ∃ c : degreeObjects C n, Nonempty (IsInitial c)) :
    WeakEquivalence (diagonalLocalization C) := by
  apply diagonalLocalization_weak_of_native_units C
  intro n
  obtain ⟨c, ⟨hc⟩⟩ := hC n
  exact unit_nerve_weak_of_initial c hc

theorem diagonalLocalization_weak_of_strict_groupoid (C : SimplicialCat.{u, u})
    (hC : IsStrictGroupoid C) : WeakEquivalence (diagonalLocalization C) := by
  apply diagonalLocalization_weak_of_native_units C
  intro n
  letI : Groupoid.{u, u} (degreeObjects C n) :=
    Groupoid.ofIsIso (fun {x y} a ↦ hC n x y a)
  exact unit_nerve_weak_of_groupoid (degreeObjects C n)

end
end DaggerOriginalDegreewiseCompletionCriterion
