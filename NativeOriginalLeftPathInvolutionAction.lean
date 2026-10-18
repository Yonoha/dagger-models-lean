import NativeOriginalLeftPathEndpointTransport
import NativeOriginalC2InvolutionAction
import NativeOriginalC2RealizationMapping

/-! The SAME natural left/path comparison is equivariant for the ORIGINAL C2. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial HomotopicalAlgebra
open DaggerOriginalQuasicategoryLeftMappingSpace DaggerOriginalFullVertexSubcomplex
open DaggerNativeOriginalLeftPathEndpointTransport
open DaggerOriginalDaggerRealizationC2Action DaggerNativeOriginalC2InvolutionAction
open DaggerNativeOriginalC2RealizationMapping
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeOriginalLeftPathInvolutionAction
noncomputable section

variable {X : SSet.{u}} (s : X ⟶ X) (hs : s ≫ s = 𝟙 X)
variable (x y : X _⦋0⦌) (hx : s.app (op ⦋0⦌) x = x) (hy : s.app (op ⦋0⦌) y = y)

def leftEnd : End (leftMappingSpace X x y) := End.of (leftMapTo s x y x y hx hy)
def pathEnd : End (strictPathFiber X x y).toSSet := End.of (pathMapTo s x y x y hx hy)

include hs

theorem leftEnd_square : leftEnd s x y hx hy * leftEnd s x y hx hy = 1 := by
  change leftMapTo s x y x y hx hy ≫ leftMapTo s x y x y hx hy = 𝟙 _
  rw [leftMapTo_comp]
  have hid (t : X ⟶ X) (ht : t = 𝟙 X)
      (ha : t.app (op ⦋0⦌) x = x) (hb : t.app (op ⦋0⦌) y = y) :
      leftMapTo t x y x y ha hb = 𝟙 _ := by
    subst t
    exact leftMapTo_id X x y
  exact hid (s ≫ s) hs _ _

theorem pathEnd_square : pathEnd s x y hx hy * pathEnd s x y hx hy = 1 := by
  change pathMapTo s x y x y hx hy ≫ pathMapTo s x y x y hx hy = 𝟙 _
  rw [pathMapTo_comp]
  have hid (t : X ⟶ X) (ht : t = 𝟙 X)
      (ha : t.app (op ⦋0⦌) x = x) (hb : t.app (op ⦋0⦌) y = y) :
      pathMapTo t x y x y ha hb = 𝟙 _ := by
    subst t
    exact pathMapTo_id X x y
  exact hid (s ≫ s) hs _ _

def leftAction : Action SSet.{u} C2.{u} :=
  action (leftEnd s x y hx hy) (leftEnd_square s hs x y hx hy)

def pathAction : Action SSet.{u} C2.{u} :=
  action (pathEnd s x y hx hy) (pathEnd_square s hs x y hx hy)

def comparisonAction : leftAction s hs x y hx hy ⟶ pathAction s hs x y hx hy :=
  DaggerNativeOriginalC2InvolutionAction.map
    (leftEnd s x y hx hy) (leftEnd_square s hs x y hx hy)
    (pathEnd s x y hx hy) (pathEnd_square s hs x y hx hy)
    (DaggerNativeOriginalLeftMappingStrictPaths.comparison X x y)
    (comparison_naturalityTo s x y x y hx hy)

theorem comparisonAction_hom :
    (comparisonAction s hs x y hx hy).hom =
      DaggerNativeOriginalLeftMappingStrictPaths.comparison X x y := rfl

theorem comparisonAction_weak [X.KanComplex] :
    WeakEquivalence (comparisonAction s hs x y hx hy).hom :=
  DaggerNativeOriginalLeftMappingStrictPaths.comparison_weak X x y

theorem left_generator_raw (n : SimplexCategoryᵒᵖ) (v : (leftMappingSpace X x y).obj n) :
    (((leftAction s hs x y hx hy).ρ generator).asHom.app n v).val.val =
      s.app (op ((DaggerOriginalOrdinalJoinLeft.ordinalJoinLeft ⦋0⦌).obj n.unop)) v.val.val := by
  unfold leftAction
  rw [DaggerNativeOriginalC2InvolutionAction.action_generator]
  exact DaggerNativePrefixMappingTransportIso.mapTo_raw s ⦋0⦌ x y x y hx hy n v

theorem path_generator_ι :
    ((pathAction s hs x y hx hy).ρ generator).asHom ≫ (strictPathFiber X x y).ι =
      (strictPathFiber X x y).ι ≫ (ihom Δ[1]).map s := by
  unfold pathAction
  rw [DaggerNativeOriginalC2InvolutionAction.action_generator]
  exact DaggerNativeLabeledStrictPathWeak.map_ι s x y x y hx hy

def realizedEC2Comparison :
    mappingFunctor.obj (leftAction s hs x y hx hy) ⟶
      mappingFunctor.obj (pathAction s hs x y hx hy) :=
  mappingFunctor.map (comparisonAction s hs x y hx hy)

theorem realizedEC2Comparison_weak [X.KanComplex] :
    WeakEquivalence (realizedEC2Comparison s hs x y hx hy) := by
  have : WeakEquivalence (comparisonAction s hs x y hx hy).hom :=
    comparisonAction_weak s hs x y hx hy
  exact mapping_map_weak _

end
end DaggerNativeOriginalLeftPathInvolutionAction
