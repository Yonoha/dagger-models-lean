import NativeFreePathCompletionQuiverBridge
import NativeGroupoidCompletionNerveBaseCases

/-! The native categorical and quiver units have the same nerve weak-equivalence problem. -/
set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra
open DaggerNativeFreePathCompletionQuiverBridge DaggerNativeGroupoidCompletionNerveBaseCases
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeFreePathCompletionQuiverNerve
noncomputable section

variable (V : Type u) [Quiver.{u + 1} V]

def completionIso : Cat.of (FreeGroupoid (Paths V)) ≅ Cat.of (Quiver.FreeGroupoid V) where
  hom := (toQuiver V).toCatHom
  inv := (fromQuiver V).toCatHom
  hom_inv_id := congrArg CategoryTheory.Functor.toCatHom (toQuiver_fromQuiver V)
  inv_hom_id := congrArg CategoryTheory.Functor.toCatHom (fromQuiver_toQuiver V)

theorem toQuiver_nerve_weak : WeakEquivalence (nerveMap (toQuiver V)) := by
  change WeakEquivalence (nerveFunctor.map (completionIso V).hom)
  infer_instance

theorem unit_nerve_square :
    nerveMap (FreeGroupoid.of (Paths V)) ≫ nerveMap (toQuiver V) =
      nerveMap (pathUnit V) := by
  change nerveMap (FreeGroupoid.of (Paths V) ⋙ toQuiver V) = _
  rw [categorical_unit_square]

theorem unit_nerve_weak_iff :
    WeakEquivalence (nerveMap (FreeGroupoid.of (Paths V))) ↔
      WeakEquivalence (nerveMap (pathUnit V)) := by
  have := toQuiver_nerve_weak V
  rw [← unit_nerve_square]
  exact (weakEquivalence_postcomp_iff _ _).symm

end
end DaggerNativeFreePathCompletionQuiverNerve
