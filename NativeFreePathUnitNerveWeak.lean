import NativeRootedSpineContractibility
import NativeLiftedQuiverParents
import NativePathUnitCommaSpine
import NativePathUnitObjects
import NativeFreePathCompletionQuiverNerve

/-! The actual groupoid-completion unit of every native free-path category is nerve weak. -/
set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra
open DaggerNativeRootedQuiverPairingData DaggerNativeRootedSpineContractibility
open DaggerNativeFreePathCompletionQuiverBridge DaggerNativeFreePathCompletionQuiverNerve
open DaggerNativePathUnitLiftedQuiver DaggerNativeLiftedQuiverHeight
open DaggerNativeLiftedQuiverParents DaggerNativePathUnitCommaSpine DaggerNativePathUnitObjects
open DaggerSSetGluing DaggerOriginalProductGadget
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeFreePathUnitNerveWeak
noncomputable section

variable (V : Type u) [Quiver.{u + 1} V]

def liftedData (a : V) : Data (Vertex V ((pathUnit V).obj (show Paths V from a))) where
  root := root V a
  height := height V a
  height_zero_iff := height_zero_iff V a
  edge_height := height_edge V a
  unique_parent := existsUnique_parent V a

theorem comma_point_weak (d : Quiver.FreeGroupoid V) :
    WeakEquivalence (pointMap (nerve (StructuredArrow d (pathUnit V)))) := by
  obtain ⟨a, rfl⟩ := pathUnit_obj_surjective V d
  have := spine_point_weak (liftedData V a)
  have := spineToComma_weak V ((pathUnit V).obj a)
  have he : spineToComma V ((pathUnit V).obj a) ≫
      pointMap (nerve (StructuredArrow ((pathUnit V).obj a) (pathUnit V))) =
        pointMap (DaggerNativeGeneratorSpineSimplices.spine
          (Vertex V ((pathUnit V).obj a))) := pointIsTerminal.hom_ext _ _
  exact weakEquivalence_of_precomp_of_fac he

theorem comma_point_GW (d : Quiver.FreeGroupoid V) :
    GW (pointMap (nerve (StructuredArrow d (pathUnit V)))) :=
  (weakEquivalence_iff_GW _).mp (comma_point_weak V d)

theorem pathUnit_nerve_weak : WeakEquivalence (nerveMap (pathUnit V)) :=
  (weakEquivalence_iff_GW _).mpr
    (DaggerNativeDualTheoremA.nerveMap_GW (pathUnit V) (comma_point_GW V))

theorem unit_nerve_weak : WeakEquivalence (nerveMap (FreeGroupoid.of (Paths V))) :=
  (unit_nerve_weak_iff V).mpr (pathUnit_nerve_weak V)

end
end DaggerNativeFreePathUnitNerveWeak
