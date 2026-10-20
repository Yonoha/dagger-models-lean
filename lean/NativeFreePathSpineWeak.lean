import NativeFreePathPairingRegularity
import TopCatModelCategory.ModelCategorySSet

/-! The actual free-path weighted-spine inclusion is a Kan-Quillen trivial cofibration. -/
set_option autoImplicit false
open CategoryTheory Simplicial HomotopicalAlgebra
open DaggerNativeFreePathNerveWeight DaggerNativeFreePathPairingRegularity
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeFreePathSpineWeak

variable (V : Type u) [Quiver.{u + 1} V]

theorem generatorSpine_trivialCofibration :
    trivialCofibrations SSet.{u} (generatorSpine V).ι := by
  rw [← fibrations_llp]
  exact generatorSpine_anodyne V

theorem generatorSpine_weak : WeakEquivalence (generatorSpine V).ι :=
  (mem_trivialCofibrations_iff _).mp (generatorSpine_trivialCofibration V) |>.2

end DaggerNativeFreePathSpineWeak
