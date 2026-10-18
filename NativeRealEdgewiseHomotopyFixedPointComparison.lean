import NativeRealEdgewiseContinuousComparison
import OriginalEC2MappingSingModelPreservation

/-! The original literal EC2 mapping functor sends the SAME palindromic map to a weak comparison. -/
set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra DaggerModels
open DaggerNativeRealEdgewiseContinuousComparison DaggerNativeRealEdgewiseGeometricWeak
open DaggerOriginalEC2HomotopyFixedPointFunctor DaggerOriginalEC2MappingSingModelPreservation
open scoped TopCat.modelCategory SSet.modelCategoryQuillen DaggerOriginalBorelModelCategory
universe u
namespace DaggerNativeRealEdgewiseHomotopyFixedPointComparison
noncomputable section

theorem continuousComparison_weak (X : DaggerSSet.{u}) :
    WeakEquivalence (continuousComparison X).hom := by
  apply (DaggerOriginalBorelModelCategory.weakEquivalence_iff_underlying _).mpr
  exact comparison_weak X.toSSet

def edgewiseHomotopyFixedPointFunctor : DaggerSSet.{u} ⥤ SSet.{u} :=
  realizedEdgewiseContinuousFunctor ⋙ mappingSingFunctor

def homotopyFixedPointComparison :
    edgewiseHomotopyFixedPointFunctor.{u} ⟶ daggerHomotopyFixedPointFunctor :=
  Functor.whiskerRight naturalContinuousComparison mappingSingFunctor

theorem homotopyFixedPointComparison_app (X : DaggerSSet.{u}) :
    homotopyFixedPointComparison.app X = mappingSingFunctor.map (continuousComparison X) := rfl

theorem homotopyFixedPointComparison_weak (X : DaggerSSet.{u}) :
    WeakEquivalence (homotopyFixedPointComparison.app X) := by
  have : WeakEquivalence (continuousComparison X).hom := continuousComparison_weak X
  exact mappingSing_map_weakEquivalence (continuousComparison X)

end
end DaggerNativeRealEdgewiseHomotopyFixedPointComparison
