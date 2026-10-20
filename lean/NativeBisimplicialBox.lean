import NativeBisimplicialHorizontalMapping

/-! The external box retains ordered pairs of original horizontal and vertical simplices. -/
set_option autoImplicit false
open CategoryTheory MonoidalCategory Simplicial Opposite
open DaggerNativeBisimplicialHorizontalMapping
universe u
namespace DaggerNativeBisimplicialBox
noncomputable section

def boxRow (T : Type u) (A : SSet.{u}) : SSet.{u} :=
  ((Functor.const SimplexCategoryᵒᵖ).obj T : SSet.{u}) ⊗ A

def box (K A : SSet.{u}) : BiSSet.{u} where
  obj h := boxRow (K.obj h) A
  map α :=
    { app := fun _ p ↦ (K.map α p.1, p.2)
      naturality := by intros; rfl }
  map_id h := by
    apply NatTrans.ext
    funext v p
    change (K.map (𝟙 h) p.1, p.2) = p
    rw [K.map_id]
    rfl
  map_comp α β := by
    apply NatTrans.ext
    funext v p
    change (K.map (α ≫ β) p.1, p.2) = (K.map β (K.map α p.1), p.2)
    rw [K.map_comp]
    rfl

def boxMap {K L A B : SSet.{u}} (i : K ⟶ L) (j : A ⟶ B) : box K A ⟶ box L B where
  app h :=
    { app := fun v p ↦ (i.app h p.1, j.app v p.2)
      naturality := by
        intro v w α
        funext p
        exact Prod.ext rfl (congrFun (j.naturality α) p.2) }
  naturality h l β := by
    apply NatTrans.ext
    funext v p
    exact Prod.ext (congrFun (i.naturality β) p.1) rfl

theorem boxMap_id (K A : SSet.{u}) : boxMap (𝟙 K) (𝟙 A) = 𝟙 (box K A) := by
  apply NatTrans.ext
  funext h
  apply NatTrans.ext
  rfl

theorem boxMap_comp {K L M A B C : SSet.{u}} (i : K ⟶ L) (i' : L ⟶ M)
    (j : A ⟶ B) (j' : B ⟶ C) :
    boxMap (i ≫ i') (j ≫ j') = boxMap i j ≫ boxMap i' j' := by
  apply NatTrans.ext
  funext h
  apply NatTrans.ext
  rfl

end
end DaggerNativeBisimplicialBox
