import NativePathUnitLiftedQuiver

/-! Every original native free-groupoid object is the image of its original base vertex. -/
set_option autoImplicit false
open CategoryTheory
open DaggerNativeFreePathCompletionQuiverBridge DaggerNativePathUnitLiftedQuiver
universe u
namespace DaggerNativePathUnitObjects

variable (V : Type u) [Quiver.{u + 1} V]

theorem pathUnit_obj_surjective : Function.Surjective (pathUnit V).obj := by
  intro d
  exact ⟨d.as, rfl⟩

def baseVertex (d : Quiver.FreeGroupoid V) : Vertex V d := ⟨d.as, 𝟙 d⟩

end DaggerNativePathUnitObjects
