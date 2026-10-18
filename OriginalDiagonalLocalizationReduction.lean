import NativeBisimplicialDiagonalWeak
import OriginalLocalizationHomWeakFromDiagonal

/-! The actual localization diagonal preserves degreewise weakness and exact arrow retracts. -/
set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra DaggerModels
open DaggerOriginalSimplicialCategoryDiagonalNerve DaggerOriginalSimplicialDegreeCategory
open DaggerOriginalSimplicialGroupoidCompletion DaggerOriginalSimplicialGroupoidCompletionFunctor
open DaggerNativeBisimplicialDiagonalWeak DaggerOriginalAmbientDaggerPiZeroGroupoid
open DaggerOriginalLocalizationHomWeakFromDiagonal
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerOriginalDiagonalLocalizationReduction
noncomputable section

def diagonalLocalizationUnit :
    diagonalNerveFunctor.{u} ⟶ completionFunctor ⋙ diagonalNerveFunctor :=
  Functor.whiskerRight localizationNatTrans diagonalNerveFunctor

theorem diagonalLocalization_weak_of_degree_nerve (C : SimplicialCat.{u, u})
    (hC : ∀ n, WeakEquivalence (nerveMap (degreeFunctor (localization C) n))) :
    WeakEquivalence (diagonalLocalization C) :=
  diagonal_map_weak (bisimplicialNerveFunctor.map (localization C)) hC

def diagonalLocalizationRetract {C D : SimplicialCat.{u, u}} (i : C ⟶ D) (r : D ⟶ C)
    (hi : i ≫ r = 𝟙 C) : RetractArrow (diagonalLocalization C) (diagonalLocalization D) where
  i := Arrow.homMk (diagonalNerveFunctor.map i)
    ((completionFunctor ⋙ diagonalNerveFunctor).map i) (diagonalLocalizationUnit.naturality i)
  r := Arrow.homMk (diagonalNerveFunctor.map r)
    ((completionFunctor ⋙ diagonalNerveFunctor).map r) (diagonalLocalizationUnit.naturality r)
  retract := by
    apply Arrow.hom_ext
    · change diagonalNerveFunctor.map i ≫ diagonalNerveFunctor.map r = 𝟙 _
      rw [← CategoryTheory.Functor.map_comp, hi, CategoryTheory.Functor.map_id]
    · change (completionFunctor ⋙ diagonalNerveFunctor).map i ≫
        (completionFunctor ⋙ diagonalNerveFunctor).map r = 𝟙 _
      rw [← CategoryTheory.Functor.map_comp, hi, CategoryTheory.Functor.map_id]

theorem diagonalLocalization_weak_of_retract {C D : SimplicialCat.{u, u}}
    (i : C ⟶ D) (r : D ⟶ C) (hi : i ≫ r = 𝟙 C)
    (hD : WeakEquivalence (diagonalLocalization D)) :
    WeakEquivalence (diagonalLocalization C) := by
  have := hD
  exact ⟨MorphismProperty.of_retract (diagonalLocalizationRetract i r hi)
    (mem_weakEquivalences (diagonalLocalization D))⟩

theorem diagonalLocalization_weak_of_retract_degree_nerve {C D : SimplicialCat.{u, u}}
    (i : C ⟶ D) (r : D ⟶ C) (hi : i ≫ r = 𝟙 C)
    (hD : ∀ n, WeakEquivalence (nerveMap (degreeFunctor (localization D) n))) :
    WeakEquivalence (diagonalLocalization C) :=
  diagonalLocalization_weak_of_retract i r hi (diagonalLocalization_weak_of_degree_nerve D hD)

theorem localizationHom_weak_of_retract_degree_nerve {C D : SimplicialCat.{u, u}}
    (hC : HasActualComponentGroupoid C) (i : C ⟶ D) (r : D ⟶ C) (hi : i ≫ r = 𝟙 C)
    (hD : ∀ n, WeakEquivalence (nerveMap (degreeFunctor (localization D) n)))
    (x y : C.Obj) : WeakEquivalence (localizationHom C x y) :=
  localizationHom_weak_of_diagonal C hC
    (diagonalLocalization_weak_of_retract_degree_nerve i r hi hD) x y

end
end DaggerOriginalDiagonalLocalizationReduction
