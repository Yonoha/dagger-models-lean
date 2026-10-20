import NativeRealEdgewiseComparisonWeakReduction
import NativeRealEdgewiseSingularHomotopy
import NativeRealEdgewiseRealizationC2Comparison

/-! Weakness of the SAME original equivariant, vertex-preserving palindromic realization map. -/
set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra DaggerModels
open DaggerNativeRealEdgewiseRealizationComparison
open DaggerNativeRealEdgewiseRealizationC2Comparison
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeRealEdgewiseGeometricWeak

theorem comparison_weak (X : SSet.{u}) : WeakEquivalence (comparison X) :=
  DaggerNativeRealEdgewiseComparisonWeakReduction.comparison_weak_of_homotopy X
    (DaggerNativeRealEdgewiseSingularHomotopy.transposeHomotopy X)

theorem comparison_singular_W (X : SSet.{u}) :
    SSet.KanComplex.W (TopCat.toSSet.map (comparison X)) :=
  (TopCat.modelCategory.weakEquivalence_iff _).mp (comparison_weak X)

theorem comparisonActionMap_weak (X : DaggerSSet.{u}) :
    WeakEquivalence (comparisonActionMap X).hom := comparison_weak X.toSSet

theorem comparisonActionMap_singular_W (X : DaggerSSet.{u}) :
    SSet.KanComplex.W (TopCat.toSSet.map (comparisonActionMap X).hom) :=
  comparison_singular_W X.toSSet

end DaggerNativeRealEdgewiseGeometricWeak
