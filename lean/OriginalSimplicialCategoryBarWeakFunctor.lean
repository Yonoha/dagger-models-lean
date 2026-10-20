import OriginalSimplicialCategoryBarWeakContractibility

/-!
# Weak equivalences on every original endpoint bar component

The actual component map induced by any original enriched functor commutes
with the actual augmentations. Both augmentations are weak equivalences,
so the native two-out-of-three theorem proves the actual component map weak.
This does not assert that a total coproduct map with arbitrary object map is weak.
-/
set_option autoImplicit false
open CategoryTheory Simplicial DaggerModels HomotopicalAlgebra
open DaggerOriginalSimplicialCategoryBarFunctor
open DaggerOriginalSimplicialCategoryBarWeakContractibility
universe u
namespace DaggerOriginalSimplicialCategoryBarWeakFunctor
noncomputable section

/-- The entire original endpoint component map commutes with its actual augmentation. -/
theorem barComponentMap_augmentation {C D : SimplicialCat.{u, u}} (F : C ⟶ D)
    (y : C.Obj) :
    barComponentMap F y ≫ barAugmentation D (F.obj y) = barAugmentation C y :=
  SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

/-- Any whole original enriched functor induces a weak equivalence on each bar component. -/
theorem barComponentMap_weakEquivalence {C D : SimplicialCat.{u, u}} (F : C ⟶ D)
    (y : C.Obj) : WeakEquivalence (barComponentMap F y) := by
  have : WeakEquivalence (barAugmentation C y) := barAugmentation_weakEquivalence C y
  have : WeakEquivalence (barAugmentation D (F.obj y)) :=
    barAugmentation_weakEquivalence D (F.obj y)
  exact weakEquivalence_of_postcomp_of_fac (barComponentMap_augmentation F y)

end
end DaggerOriginalSimplicialCategoryBarWeakFunctor
