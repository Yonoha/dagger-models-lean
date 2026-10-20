import NativeOriginalCoslicePathMap
import NativeHornPointWeakEquivalences
import NativeWeakSquareNativeFibres
import OriginalQuasicategoryLeftMappingSpace

/-! The ORIGINAL coslice and native based-path total spaces are contractible over SAME X. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial MonoidalCategory CartesianMonoidalCategory
open HomotopicalAlgebra
open DaggerOriginalSimplexCoslice DaggerOriginalVertexCosliceContraction
open DaggerOriginalKanVertexCosliceFibration DaggerOriginalQuasicategoryLeftMappingSpace
open DaggerNativeOriginalCoslicePathMap DaggerNativeHornPointWeakEquivalences
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeOriginalCosliceBasedPaths
noncomputable section

def toBased (X : SSet.{u}) (x : X _⦋0⦌) :
    simplexCoslice ⦋0⦌ X x ⟶ (X.path₀ x).toSSet :=
  SSet.Subcomplex.lift (comparison X x) (by
    intro n z hz
    obtain ⟨s, rfl⟩ := hz
    apply (SSet.Subcomplex.mem_fiber_obj_iff X.pathEv₀ x _).mpr
    exact congrFun (NatTrans.congr_app (comparison_zero X x) n) s)

theorem toBased_ι (X : SSet.{u}) (x : X _⦋0⦌) :
    toBased X x ≫ (X.path₀ x).ι = comparison X x := SSet.Subcomplex.lift_ι _ _

theorem toBased_triangle (X : SSet.{u}) (x : X _⦋0⦌) :
    toBased X x ≫ X.path₀π x = cosliceProjection ⦋0⦌ X x := by
  rw [SSet.path₀π, ← Category.assoc, toBased_ι, comparison_one]

/-- The actual map is weak for ALL simplicial sets: both unchanged total spaces contract. -/
theorem toBased_weak (X : SSet.{u}) (x : X _⦋0⦌) : WeakEquivalence (toBased X x) := by
  have : WeakEquivalence (toUnit (simplexCoslice ⦋0⦌ X x)) :=
    contractible_terminal_weak (vertexCosliceContractible X x)
  have : WeakEquivalence (toUnit (X.path₀ x).toSSet) :=
    contractible_terminal_weak (SSet.contractiblePath₀ X x)
  have h : toBased X x ≫ toUnit (X.path₀ x).toSSet =
      toUnit (simplexCoslice ⦋0⦌ X x) := isTerminalTensorUnit.hom_ext _ _
  exact weakEquivalence_of_postcomp_of_fac h

def fiberMap (X : SSet.{u}) (x y : X _⦋0⦌) :
    leftMappingSpace X x y ⟶ (SSet.Subcomplex.fiber (X.path₀π x) y).toSSet :=
  SSet.Subcomplex.mapFiber (cosliceProjection ⦋0⦌ X x) (X.path₀π x)
    (toBased X x) (𝟙 X) (by rw [Category.comp_id, toBased_triangle]) y y rfl

/-- Native weak-square fiber recognition applies at every SAME endpoint, including x = y. -/
theorem fiberMap_weak (X : SSet.{u}) [X.KanComplex] (x y : X _⦋0⦌) :
    WeakEquivalence (fiberMap X x y) := by
  have : Fibration (cosliceProjection ⦋0⦌ X x) := vertex_coslice_projection_fibration X x
  have : Fibration (X.path₀π x) := inferInstance
  have : WeakEquivalence (toBased X x) := toBased_weak X x
  exact DaggerNativeWeakSquareNativeFibres.native_mapFiber_weak _ _ _ _ _ _ _ _

end
end DaggerNativeOriginalCosliceBasedPaths
