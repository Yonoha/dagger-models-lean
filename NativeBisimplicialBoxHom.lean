import NativeBisimplicialBox

/-! Actual box maps are the existing horizontal mapping object's vertical simplices. -/
set_option autoImplicit false
open CategoryTheory Simplicial Opposite
open DaggerNativeBisimplicialHorizontalMapping DaggerNativeBisimplicialBox
universe u
namespace DaggerNativeBisimplicialBoxHom
noncomputable section

def boxCurry (K A : SSet.{u}) (X : BiSSet.{u}) (f : box K A ⟶ X) :
    A ⟶ horizontalMapping K X where
  app v b :=
    { app := fun h a ↦ (f.app h).app v (a, b)
      naturality := by
        intro h l α
        funext a
        exact congrFun (NatTrans.congr_app (f.naturality α) v) (a, b) }
  naturality v w β := by
    funext b
    apply NatTrans.ext
    funext h a
    exact congrFun ((f.app h).naturality β) (a, b)

def boxUncurry (K A : SSet.{u}) (X : BiSSet.{u})
    (g : A ⟶ horizontalMapping K X) : box K A ⟶ X where
  app h :=
    { app := fun v p ↦ (g.app v p.2).app h p.1
      naturality := by
        intro v w β
        funext p
        exact congrFun (NatTrans.congr_app (congrFun (g.naturality β) p.2) h) p.1 }
  naturality h l α := by
    apply NatTrans.ext
    funext v p
    exact congrFun ((g.app v p.2).naturality α) p.1

def boxHomEquiv (K A : SSet.{u}) (X : BiSSet.{u}) :
    (box K A ⟶ X) ≃ (A ⟶ horizontalMapping K X) where
  toFun := boxCurry K A X
  invFun := boxUncurry K A X
  left_inv f := by
    apply NatTrans.ext
    funext h
    apply NatTrans.ext
    rfl
  right_inv g := by
    apply NatTrans.ext
    funext v b
    apply NatTrans.ext
    rfl

theorem boxCurry_value (K A : SSet.{u}) (X : BiSSet.{u}) (f : box K A ⟶ X)
    (h v : SimplexCategoryᵒᵖ) (a : K.obj h) (b : A.obj v) :
    ((boxCurry K A X f).app v b).app h a = (f.app h).app v (a, b) := rfl

theorem boxUncurry_value (K A : SSet.{u}) (X : BiSSet.{u})
    (g : A ⟶ horizontalMapping K X) (h v : SimplexCategoryᵒᵖ)
    (a : K.obj h) (b : A.obj v) :
    ((boxUncurry K A X g).app h).app v (a, b) = (g.app v b).app h a := rfl

theorem boxCurry_pre {K L A B : SSet.{u}} (i : K ⟶ L) (j : A ⟶ B)
    (X : BiSSet.{u}) (f : box L B ⟶ X) :
    boxCurry K A X (boxMap i j ≫ f) = j ≫ boxCurry L B X f ≫ horizontalPre i X := by
  apply NatTrans.ext
  funext v b
  apply NatTrans.ext
  rfl

theorem boxCurry_post (K A : SSet.{u}) {X Y : BiSSet.{u}} (f : X ⟶ Y)
    (g : box K A ⟶ X) :
    boxCurry K A Y (g ≫ f) = boxCurry K A X g ≫ horizontalMap K f := by
  apply NatTrans.ext
  funext v b
  apply NatTrans.ext
  rfl

end
end DaggerNativeBisimplicialBoxHom
