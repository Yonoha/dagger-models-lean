import OriginalSimplicialCategoryWholeBarWeakEquivalence

/-!
# The actual original localization induces a weak equivalence on the entire bar

The actual degreewise groupoid completion unit is identity on original objects.
Its whole original bar map therefore commutes with both actual augmentations
to the very same object-indexed standard points. Native two-out-of-three proves
this whole map weak, without assuming the diagonal localization or its Hom maps weak.
-/
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Simplicial DaggerModels HomotopicalAlgebra
open DaggerOriginalSimplicialGroupoidCompletion
open DaggerOriginalSimplicialCategoryDiagonalNerve
open DaggerOriginalSimplicialCategoryBarConstruction
open DaggerOriginalSimplicialCategoryBarFunctor
open DaggerOriginalSimplicialCategoryBarWeakContractibility
open DaggerOriginalSimplicialCategoryBarWeakFunctor
open DaggerOriginalSimplicialCategoryWholeBarWeakEquivalence
universe u
namespace DaggerOriginalSimplicialCategoryWholeBarLocalization
noncomputable section

/-- The original whole bar map induced by the actual original completion unit. -/
def wholeBarLocalization (C : SimplicialCat.{u, u}) : bar C ⟶ bar (completion C) :=
  barMap (localization C)

/-- The actual unit keeps the same original endpoint points in the entire bar augmentation. -/
theorem wholeBarLocalization_augmentation (C : SimplicialCat.{u, u}) :
    wholeBarLocalization C ≫ wholeBarAugmentation (completion C) =
      wholeBarAugmentation C := by
  apply Sigma.hom_ext
  intro y
  change barInclusion C y ≫
      (wholeBarLocalization C ≫ wholeBarAugmentation (completion C)) =
    barInclusion C y ≫ wholeBarAugmentation C
  calc
    barInclusion C y ≫ (wholeBarLocalization C ≫ wholeBarAugmentation (completion C)) =
        (barComponentMap (localization C) y ≫ barInclusion (completion C) y) ≫
          wholeBarAugmentation (completion C) := by
      rw [← Category.assoc]
      exact congrArg (fun f ↦ f ≫ wholeBarAugmentation (completion C))
        (barInclusion_map (localization C) y)
    _ = (barComponentMap (localization C) y ≫ barAugmentation (completion C) y) ≫
        Sigma.ι (fun _ : C.Obj ↦ (Δ[0] : SSet.{u})) y := by
      rw [Category.assoc]
      change barComponentMap (localization C) y ≫
          (Sigma.ι (barComponent (completion C)) y ≫
            Limits.Sigma.map (barAugmentation (completion C))) = _
      rw [Sigma.ι_map, ← Category.assoc]
      rfl
    _ = barAugmentation C y ≫ Sigma.ι (fun _ : C.Obj ↦ (Δ[0] : SSet.{u})) y := by
      exact congrArg (fun f ↦ f ≫ Sigma.ι (fun _ : C.Obj ↦ (Δ[0] : SSet.{u})) y)
        (barComponentMap_augmentation (localization C) y)
    _ = barInclusion C y ≫ wholeBarAugmentation C :=
      (Sigma.ι_map (barAugmentation C) y).symm

/-- The actual whole bar map of the actual completion unit is a weak equivalence. -/
theorem wholeBarLocalization_weakEquivalence (C : SimplicialCat.{u, u}) :
    WeakEquivalence (wholeBarLocalization C) := by
  have : WeakEquivalence (wholeBarAugmentation C) := wholeBarAugmentation_weakEquivalence C
  have : WeakEquivalence (wholeBarAugmentation (completion C)) :=
    wholeBarAugmentation_weakEquivalence (completion C)
  exact weakEquivalence_of_postcomp_of_fac (wholeBarLocalization_augmentation C)

/-- The actual bar and diagonal maps of the actual unit form their original comparison square. -/
theorem wholeBarLocalization_square (C : SimplicialCat.{u, u}) :
    CommSq (wholeBarLocalization C) (barProjection C)
      (barProjection (completion C)) (diagonalLocalization C) :=
  ⟨barProjection_natural (localization C)⟩

end
end DaggerOriginalSimplicialCategoryWholeBarLocalization
