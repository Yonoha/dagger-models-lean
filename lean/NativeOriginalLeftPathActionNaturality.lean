import NativeOriginalLeftPathInvolutionAction

/-! Equivariant naturality retains EVERY original intertwiner and BOTH endpoint equations. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial
open DaggerOriginalQuasicategoryLeftMappingSpace DaggerOriginalFullVertexSubcomplex
open DaggerNativeOriginalLeftPathEndpointTransport DaggerNativeOriginalLeftPathInvolutionAction
open DaggerNativePrefixMappingTransportIso DaggerOriginalOrdinalJoinLeft
universe u
namespace DaggerNativeOriginalLeftPathActionNaturality
noncomputable section

variable {X Y : SSet.{u}} (s : X ⟶ X) (hs : s ≫ s = 𝟙 X)
variable (t : Y ⟶ Y) (ht : t ≫ t = 𝟙 Y)
variable (x y : X _⦋0⦌) (a b : Y _⦋0⦌)
variable (hx : s.app (op ⦋0⦌) x = x) (hy : s.app (op ⦋0⦌) y = y)
variable (ha : t.app (op ⦋0⦌) a = a) (hb : t.app (op ⦋0⦌) b = b)
variable (f : X ⟶ Y) (hf : s ≫ f = f ≫ t)
variable (hfx : f.app (op ⦋0⦌) x = a) (hfy : f.app (op ⦋0⦌) y = b)

include hf

theorem left_comm :
    leftEnd s x y hx hy ≫ leftMapTo f x y a b hfx hfy =
      leftMapTo f x y a b hfx hfy ≫ leftEnd t a b ha hb := by
  apply NatTrans.ext
  funext n v
  apply Subtype.ext
  apply Subtype.ext
  change ((mapTo f ⦋0⦌ x y a b hfx hfy).app n
    ((mapTo s ⦋0⦌ x y x y hx hy).app n v)).val.val =
      ((mapTo t ⦋0⦌ a b a b ha hb).app n
        ((mapTo f ⦋0⦌ x y a b hfx hfy).app n v)).val.val
  rw [mapTo_raw, mapTo_raw, mapTo_raw, mapTo_raw]
  exact congrFun (NatTrans.congr_app hf (op ((ordinalJoinLeft ⦋0⦌).obj n.unop))) v.val.val

theorem path_comm :
    pathEnd s x y hx hy ≫ pathMapTo f x y a b hfx hfy =
      pathMapTo f x y a b hfx hfy ≫ pathEnd t a b ha hb := by
  change pathMapTo s x y x y hx hy ≫ pathMapTo f x y a b hfx hfy =
    pathMapTo f x y a b hfx hfy ≫ pathMapTo t a b a b ha hb
  rw [pathMapTo_comp, pathMapTo_comp]
  have hcongr (p q : X ⟶ Y) (h : p = q)
      (hpx : p.app (op ⦋0⦌) x = a) (hpy : p.app (op ⦋0⦌) y = b)
      (hqx : q.app (op ⦋0⦌) x = a) (hqy : q.app (op ⦋0⦌) y = b) :
      pathMapTo p x y a b hpx hpy = pathMapTo q x y a b hqx hqy := by
    subst q
    rfl
  exact hcongr (s ≫ f) (f ≫ t) hf _ _ _ _

def leftActionMap : leftAction s hs x y hx hy ⟶ leftAction t ht a b ha hb :=
  DaggerNativeOriginalC2InvolutionAction.map
    (leftEnd s x y hx hy) (leftEnd_square s hs x y hx hy)
    (leftEnd t a b ha hb) (leftEnd_square t ht a b ha hb)
    (leftMapTo f x y a b hfx hfy) (left_comm s t x y a b hx hy ha hb f hf hfx hfy)

def pathActionMap : pathAction s hs x y hx hy ⟶ pathAction t ht a b ha hb :=
  DaggerNativeOriginalC2InvolutionAction.map
    (pathEnd s x y hx hy) (pathEnd_square s hs x y hx hy)
    (pathEnd t a b ha hb) (pathEnd_square t ht a b ha hb)
    (pathMapTo f x y a b hfx hfy) (path_comm s t x y a b hx hy ha hb f hf hfx hfy)

theorem comparison_naturality :
    leftActionMap s hs t ht x y a b hx hy ha hb f hf hfx hfy ≫
        comparisonAction t ht a b ha hb =
      comparisonAction s hs x y hx hy ≫
        pathActionMap s hs t ht x y a b hx hy ha hb f hf hfx hfy := by
  apply Action.hom_ext
  exact comparison_naturalityTo f x y a b hfx hfy

end
end DaggerNativeOriginalLeftPathActionNaturality
