import NativeOriginalLeftPathNaturality
import NativePrefixMappingTransportIso
import NativeLabeledStrictPathWeak

/-! Keep BOTH original endpoints while transporting the SAME left/path comparison. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial
open DaggerOriginalQuasicategoryLeftMappingSpace DaggerOriginalLeftMappingFunctoriality
open DaggerOriginalFullVertexSubcomplex DaggerNativePrefixMappingTransportIso
universe u
namespace DaggerNativeOriginalLeftPathEndpointTransport
noncomputable section

def leftMapTo {X Y : SSet.{u}} (f : X ⟶ Y) (x y : X _⦋0⦌) (a b : Y _⦋0⦌)
    (hx : f.app (op ⦋0⦌) x = a) (hy : f.app (op ⦋0⦌) y = b) :
    leftMappingSpace X x y ⟶ leftMappingSpace Y a b := mapTo f ⦋0⦌ x y a b hx hy

def pathMapTo {X Y : SSet.{u}} (f : X ⟶ Y) (x y : X _⦋0⦌) (a b : Y _⦋0⦌)
    (hx : f.app (op ⦋0⦌) x = a) (hy : f.app (op ⦋0⦌) y = b) :
    (strictPathFiber X x y).toSSet ⟶ (strictPathFiber Y a b).toSSet :=
  DaggerNativeLabeledStrictPathWeak.map f x y a b hx hy

theorem comparison_naturalityTo {X Y : SSet.{u}} (f : X ⟶ Y)
    (x y : X _⦋0⦌) (a b : Y _⦋0⦌)
    (hx : f.app (op ⦋0⦌) x = a) (hy : f.app (op ⦋0⦌) y = b) :
    leftMapTo f x y a b hx hy ≫ DaggerNativeOriginalLeftMappingStrictPaths.comparison Y a b =
      DaggerNativeOriginalLeftMappingStrictPaths.comparison X x y ≫ pathMapTo f x y a b hx hy := by
  subst a
  subst b
  change leftMappingMap f x y ≫ DaggerNativeOriginalLeftMappingStrictPaths.comparison Y
    (f.app (op ⦋0⦌) x) (f.app (op ⦋0⦌) y) =
      DaggerNativeOriginalLeftMappingStrictPaths.comparison X x y ≫
        DaggerNativeLabeledStrictPathWeak.map f x y _ _ rfl rfl
  rw [DaggerNativeLabeledStrictPathWeak.map_image]
  exact DaggerNativeOriginalLeftPathNaturality.comparison_naturality f x y

theorem leftMapTo_id (X : SSet.{u}) (x y : X _⦋0⦌) :
    leftMapTo (𝟙 X) x y x y rfl rfl = 𝟙 _ := by
  apply NatTrans.ext
  funext n s
  apply Subtype.ext
  apply Subtype.ext
  exact mapTo_raw (𝟙 X) ⦋0⦌ x y x y rfl rfl n s

theorem leftMapTo_comp {X Y Z : SSet.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (x y : X _⦋0⦌) (a b : Y _⦋0⦌) (c d : Z _⦋0⦌)
    (hx : f.app (op ⦋0⦌) x = a) (hy : f.app (op ⦋0⦌) y = b)
    (ha : g.app (op ⦋0⦌) a = c) (hb : g.app (op ⦋0⦌) b = d) :
    leftMapTo f x y a b hx hy ≫ leftMapTo g a b c d ha hb =
      leftMapTo (f ≫ g) x y c d ((congrArg (g.app _) hx).trans ha)
        ((congrArg (g.app _) hy).trans hb) := by
  apply NatTrans.ext
  funext n s
  apply Subtype.ext
  apply Subtype.ext
  change ((mapTo g ⦋0⦌ a b c d ha hb).app n
    ((mapTo f ⦋0⦌ x y a b hx hy).app n s)).val.val = _
  rw [mapTo_raw, mapTo_raw]
  exact (mapTo_raw (f ≫ g) ⦋0⦌ x y c d _ _ n s).symm

theorem pathMapTo_id (X : SSet.{u}) (x y : X _⦋0⦌) :
    pathMapTo (𝟙 X) x y x y rfl rfl = 𝟙 _ := by
  apply (cancel_mono (strictPathFiber X x y).ι).mp
  change DaggerNativeLabeledStrictPathWeak.map _ _ _ _ _ _ _ ≫ _ = _
  rw [DaggerNativeLabeledStrictPathWeak.map_ι, CategoryTheory.Functor.map_id,
    Category.comp_id, Category.id_comp]

theorem pathMapTo_comp {X Y Z : SSet.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (x y : X _⦋0⦌) (a b : Y _⦋0⦌) (c d : Z _⦋0⦌)
    (hx : f.app (op ⦋0⦌) x = a) (hy : f.app (op ⦋0⦌) y = b)
    (ha : g.app (op ⦋0⦌) a = c) (hb : g.app (op ⦋0⦌) b = d) :
    pathMapTo f x y a b hx hy ≫ pathMapTo g a b c d ha hb =
      pathMapTo (f ≫ g) x y c d ((congrArg (g.app _) hx).trans ha)
        ((congrArg (g.app _) hy).trans hb) :=
  DaggerNativeLabeledStrictPathWeak.map_comp f g x y a b c d hx hy ha hb

end
end DaggerNativeOriginalLeftPathEndpointTransport
