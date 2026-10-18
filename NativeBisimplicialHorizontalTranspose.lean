import NativeBisimplicialHorizontalMapping

/-! Transpose the actual two families of natural transformations, without replacements. -/
set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial
open DaggerNativeBisimplicialHorizontalMapping
universe u
namespace DaggerNativeBisimplicialHorizontalTranspose
noncomputable section

def transpose (K A : SSet.{u}) (X : BiSSet.{u})
    (a : A ⟶ horizontalMapping K X) : K ⟶ horizontalMapping A X.flip where
  app h x :=
    { app := fun v y ↦ (a.app v y).app h x
      naturality := by
        intro v w α
        funext y
        exact congrFun (NatTrans.congr_app (congrFun (a.naturality α) y) h) x }
  naturality h k β := by
    funext x
    apply NatTrans.ext
    funext v y
    exact congrFun ((a.app v y).naturality β) x

theorem transpose_involutive (K A : SSet.{u}) (X : BiSSet.{u})
    (a : A ⟶ horizontalMapping K X) :
    transpose A K X.flip (transpose K A X a) = a := by
  apply NatTrans.ext
  funext v y
  apply NatTrans.ext
  funext h x
  rfl

def transposeEquiv (K A : SSet.{u}) (X : BiSSet.{u}) :
    (A ⟶ horizontalMapping K X) ≃ (K ⟶ horizontalMapping A X.flip) where
  toFun := transpose K A X
  invFun := transpose A K X.flip
  left_inv := transpose_involutive K A X
  right_inv := transpose_involutive A K X.flip

theorem transpose_pre_horizontal {K L : SSet.{u}} (i : K ⟶ L) (A : SSet.{u})
    (X : BiSSet.{u}) (a : A ⟶ horizontalMapping L X) :
    transpose K A X (a ≫ horizontalPre i X) = i ≫ transpose L A X a := by
  apply NatTrans.ext
  funext h x
  apply NatTrans.ext
  funext v y
  rfl

theorem transpose_pre_vertical (K : SSet.{u}) {A B : SSet.{u}} (j : A ⟶ B)
    (X : BiSSet.{u}) (a : B ⟶ horizontalMapping K X) :
    transpose K A X (j ≫ a) = transpose K B X a ≫ horizontalPre j X.flip := by
  apply NatTrans.ext
  funext h x
  apply NatTrans.ext
  funext v y
  rfl

theorem transpose_post (K A : SSet.{u}) {X Y : BiSSet.{u}} (f : X ⟶ Y)
    (a : A ⟶ horizontalMapping K X) :
    transpose K A Y (a ≫ horizontalMap K f) = transpose K A X a ≫
      horizontalMap A
        ((flipFunctor SimplexCategoryᵒᵖ SimplexCategoryᵒᵖ (Type u)).map f) := by
  apply NatTrans.ext
  funext h x
  apply NatTrans.ext
  funext v y
  rfl

end
end DaggerNativeBisimplicialHorizontalTranspose
