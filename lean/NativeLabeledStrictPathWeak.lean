import OriginalFullVertexPathFiber
import NativeWeakSquareNativeFibres
import NativeIhomWeakBetweenKan
import SSetProductGeometric

/-! Weak equivalences between Kan complexes preserve the SAME labelled strict path fibers.
The underlying path map is the native internal-Hom postcomposition; endpoints may coincide.
-/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial MonoidalCategory HomotopicalAlgebra
open DaggerOriginalFullVertexSubcomplex
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeLabeledStrictPathWeak
noncomputable section

variable {X Y Z : SSet.{u}}

def map (f : X ⟶ Y) (a b : X _⦋0⦌) (a' b' : Y _⦋0⦌)
    (ha : f.app _ a = a') (hb : f.app _ b = b') :
    (strictPathFiber X a b : SSet.{u}) ⟶ (strictPathFiber Y a' b' : SSet.{u}) :=
  SSet.Subcomplex.mapFiber X.pathEv₀₁ Y.pathEv₀₁ ((ihom Δ[1]).map f) (f ⊗ₘ f)
    (pathEv_pair_natural f) (a, b) (a', b') (by
      change (f.app _ a, f.app _ b) = (a', b')
      rw [ha, hb])

@[reassoc]
theorem map_ι (f : X ⟶ Y) (a b : X _⦋0⦌) (a' b' : Y _⦋0⦌)
    (ha : f.app _ a = a') (hb : f.app _ b = b') :
    map f a b a' b' ha hb ≫ (strictPathFiber Y a' b').ι =
      (strictPathFiber X a b).ι ≫ (ihom Δ[1]).map f :=
  SSet.Subcomplex.mapFiber_ι _ _ _ _ _ _ _ _

theorem map_image (f : X ⟶ Y) (a b : X _⦋0⦌) :
    map f a b (f.app _ a) (f.app _ b) rfl rfl = strictPathFiberMap f a b := by
  apply (cancel_mono (strictPathFiber Y (f.app _ a) (f.app _ b)).ι).mp
  rw [map_ι]
  exact (SSet.Subcomplex.lift_ι _ _).symm

theorem map_weak [SSet.KanComplex X] [SSet.KanComplex Y] (f : X ⟶ Y)
    [WeakEquivalence f] (a b : X _⦋0⦌) (a' b' : Y _⦋0⦌)
    (ha : f.app _ a = a') (hb : f.app _ b = b') :
    WeakEquivalence (map f a b a' b' ha hb) := by
  have : WeakEquivalence ((ihom Δ[1]).map f) :=
    DaggerNativeIhomWeakBetweenKan.ihom_map_weak _ f
  have : WeakEquivalence (f ⊗ₘ f) :=
    (DaggerSSetProductGeometric.geometric_iff_weakEquivalence _).mp
      (DaggerSSetProductGeometric.tensorMap_geometric _ _
        ((DaggerSSetProductGeometric.geometric_iff_weakEquivalence _).mpr inferInstance)
        ((DaggerSSetProductGeometric.geometric_iff_weakEquivalence _).mpr inferInstance))
  exact DaggerNativeWeakSquareNativeFibres.native_mapFiber_weak _ _ _ _ _ _ _ _

theorem original_map_weak [SSet.KanComplex X] [SSet.KanComplex Y]
    (f : X ⟶ Y) [WeakEquivalence f] (a b : X _⦋0⦌) :
    WeakEquivalence (strictPathFiberMap f a b) := by
  rw [← map_image]
  exact map_weak _ _ _ _ _ _ _

theorem map_comp (f : X ⟶ Y) (g : Y ⟶ Z) (a b : X _⦋0⦌)
    (a' b' : Y _⦋0⦌) (a'' b'' : Z _⦋0⦌)
    (ha : f.app _ a = a') (hb : f.app _ b = b')
    (ha' : g.app _ a' = a'') (hb' : g.app _ b' = b'') :
    map f a b a' b' ha hb ≫ map g a' b' a'' b'' ha' hb' =
      map (f ≫ g) a b a'' b'' ((congrArg (g.app _) ha).trans ha')
        ((congrArg (g.app _) hb).trans hb') := by
  apply (cancel_mono (strictPathFiber Z a'' b'').ι).mp
  rw [Category.assoc, map_ι, map_ι_assoc, map_ι, ← Functor.map_comp]

end
end DaggerNativeLabeledStrictPathWeak
