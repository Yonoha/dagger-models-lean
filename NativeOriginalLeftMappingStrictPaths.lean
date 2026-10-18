import NativeOriginalCosliceBasedPaths
import OriginalFullVertexPathFiber

/-! The SAME native based-path fiber is the ORIGINAL paired strict path fiber. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial HomotopicalAlgebra
open DaggerOriginalSimplexCoslice DaggerOriginalQuasicategoryLeftMappingSpace
open DaggerOriginalFullVertexSubcomplex DaggerNativeOriginalCosliceBasedPaths
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeOriginalLeftMappingStrictPaths
noncomputable section

def pairedFiberHom (X : SSet.{u}) (x y : X _⦋0⦌) :
    (SSet.Subcomplex.fiber (X.path₀π x) y).toSSet ⟶ (strictPathFiber X x y).toSSet where
  app n w := ⟨w.val.val, by
    have ha := (SSet.Subcomplex.mem_fiber_obj_iff X.pathEv₀ x _).mp w.val.property
    have hb := (SSet.Subcomplex.mem_fiber_obj_iff (X.path₀π x) y _).mp w.property
    apply (SSet.Subcomplex.mem_fiber_obj_iff X.pathEv₀₁ (x, y) _).mpr
    exact Prod.ext ha hb⟩
  naturality _ _ _ := by funext w; apply Subtype.ext; rfl

def pairedFiberInv (X : SSet.{u}) (x y : X _⦋0⦌) :
    (strictPathFiber X x y).toSSet ⟶ (SSet.Subcomplex.fiber (X.path₀π x) y).toSSet where
  app n w := by
    have h := (SSet.Subcomplex.mem_fiber_obj_iff X.pathEv₀₁ (x, y) _).mp w.property
    let z : (X.path₀ x).toSSet.obj n :=
      ⟨w.val, (SSet.Subcomplex.mem_fiber_obj_iff X.pathEv₀ x _).mpr (congrArg Prod.fst h)⟩
    exact ⟨z, (SSet.Subcomplex.mem_fiber_obj_iff (X.path₀π x) y _).mpr (congrArg Prod.snd h)⟩
  naturality _ _ _ := by funext w; apply Subtype.ext; apply Subtype.ext; rfl

/-- This is an actual fiber ISO, with no Kan premise and no change of either endpoint. -/
def pairedFiberIso (X : SSet.{u}) (x y : X _⦋0⦌) :
    (SSet.Subcomplex.fiber (X.path₀π x) y).toSSet ≅ (strictPathFiber X x y).toSSet where
  hom := pairedFiberHom X x y
  inv := pairedFiberInv X x y
  hom_inv_id := by
    apply NatTrans.ext
    funext n w
    apply Subtype.ext
    apply Subtype.ext
    rfl
  inv_hom_id := by
    apply NatTrans.ext
    funext n w
    apply Subtype.ext
    rfl

theorem pairedFiberHom_ι (X : SSet.{u}) (x y : X _⦋0⦌) :
    pairedFiberHom X x y ≫ (strictPathFiber X x y).ι =
      (SSet.Subcomplex.fiber (X.path₀π x) y).ι ≫ (X.path₀ x).ι := rfl

def comparison (X : SSet.{u}) (x y : X _⦋0⦌) :
    leftMappingSpace X x y ⟶ (strictPathFiber X x y).toSSet :=
  fiberMap X x y ≫ (pairedFiberIso X x y).hom

/-- The underlying whole path is the SAME transpose of the ORIGINAL coslice contraction. -/
theorem comparison_ι (X : SSet.{u}) (x y : X _⦋0⦌) :
    comparison X x y ≫ (strictPathFiber X x y).ι =
      (leftMappingSubcomplex X x y).ι ≫ DaggerNativeOriginalCoslicePathMap.comparison X x := by
  change fiberMap X x y ≫ pairedFiberHom X x y ≫ (strictPathFiber X x y).ι = _
  rw [pairedFiberHom_ι, ← Category.assoc]
  dsimp only [fiberMap]
  rw [SSet.Subcomplex.mapFiber_ι, Category.assoc, toBased_ι]
  rfl

/-- For every native Kan X the actual original left-mapping comparison is weak. -/
theorem comparison_weak (X : SSet.{u}) [X.KanComplex] (x y : X _⦋0⦌) :
    WeakEquivalence (comparison X x y) := by
  have : WeakEquivalence (fiberMap X x y) := fiberMap_weak X x y
  unfold comparison
  infer_instance

end
end DaggerNativeOriginalLeftMappingStrictPaths
