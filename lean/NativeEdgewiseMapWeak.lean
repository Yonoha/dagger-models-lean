import NativeRealEdgewiseTargetWeak

/-! The original edgewise functor preserves every native simplicial weak equivalence. -/
set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra
open DaggerNativeRealEdgewiseSSet DaggerNativeRealEdgewiseTargetWeak
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeEdgewiseMapWeak

theorem map_weak {X Y : SSet.{u}} (f : X ⟶ Y) [WeakEquivalence f] :
    WeakEquivalence (edgewise.map f) := by
  have : WeakEquivalence (targetProjection X) := targetProjection_weak X
  have : WeakEquivalence (targetProjection Y) := targetProjection_weak Y
  have : WeakEquivalence (targetProjection X ≫ f) := inferInstance
  exact weakEquivalence_of_postcomp_of_fac (targetProjection_natural f)

end DaggerNativeEdgewiseMapWeak
