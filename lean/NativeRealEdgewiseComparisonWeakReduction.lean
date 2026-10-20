import NativeRawSSetHomotopyWeak
import NativeRealEdgewiseRealizationComparison

/-! Reduce weakness of the SAME palindromic comparison to a raw homotopy of its exact mate. -/
set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra
open DaggerNativeRealEdgewiseSSet DaggerNativeRealEdgewiseRealizationComparison
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeRealEdgewiseComparisonWeakReduction

theorem comparison_weak_of_homotopy (X : SSet.{u})
    (h : SSet.Homotopy (transpose X) (targetProjection X ≫ sSetTopAdj.unit.app X)) :
    WeakEquivalence (comparison X) := by
  have : WeakEquivalence (targetProjection X) :=
    DaggerNativeRealEdgewiseTargetWeak.targetProjection_weak X
  have : WeakEquivalence (sSetTopAdj.unit.app X) := inferInstance
  have : WeakEquivalence (transpose X) :=
    (DaggerNativeRawSSetHomotopyWeak.weak_iff h).mpr inferInstance
  have : WeakEquivalence (sSetTopAdj.unit.app (edgewise.obj X)) := inferInstance
  have hs : WeakEquivalence (TopCat.toSSet.map (comparison X)) :=
    weakEquivalence_of_precomp_of_fac (comparison_mate X)
  exact (TopCat.weakEquivalence_toSSet_map_iff (comparison X)).mp hs

end DaggerNativeRealEdgewiseComparisonWeakReduction
