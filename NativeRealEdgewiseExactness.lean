import NativeRealEdgewiseSSet
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Whiskering
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-! Reuse native precomposition to preserve the colimits and monomorphisms used by the skeleton. -/
set_option autoImplicit false
open CategoryTheory Limits
open DaggerNativeRealEdgewiseIndex DaggerNativeRealEdgewiseSSet
universe u
namespace DaggerNativeRealEdgewiseExactness

theorem edgewise_eq_whiskering : edgewise.{u} =
    (Functor.whiskeringLeft SimplexCategoryᵒᵖ SimplexCategoryᵒᵖ (Type u)).obj epsilon.op := rfl

instance preservesColimits : PreservesColimitsOfSize.{u, u} edgewise.{u} := by
  exact whiskeringLeft_preservesColimit epsilon.op

instance preservesSmallColimits : PreservesColimitsOfSize.{0, 0} edgewise.{u} := by
  exact whiskeringLeft_preservesColimit epsilon.op

instance preservesMonomorphisms : edgewise.{u}.PreservesMonomorphisms where
  preserves f _ := by
    have : ∀ n, Mono ((edgewise.map f).app n) := fun n ↦
      show Mono (f.app (epsilon.op.obj n)) from inferInstance
    exact NatTrans.mono_of_mono_app _

def targetNatural : edgewise.{u} ⟶ 𝟭 SSet.{u} where
  app := targetProjection
  naturality _ _ f := targetProjection_natural f

end DaggerNativeRealEdgewiseExactness
