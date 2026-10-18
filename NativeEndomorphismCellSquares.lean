import NativeHoIsoTriangles

/-!
# Strict squares for actual internal-Hom endomorphism simplices

Postcomposition and precomposition land in the same full native internal Hom.
Its actual functoriality proves identity and composition for every simplex degree.
-/
set_option autoImplicit false
open CategoryTheory MonoidalClosed
universe u
namespace DaggerNativeEndomorphismCellSquares

def CellSquare {X Y : SSet.{u}} (a : X ⟶ Y) {q : SimplexCategoryᵒᵖ}
    (x : ((ihom X).obj X).obj q) (y : ((ihom Y).obj Y).obj q) : Prop :=
  ((ihom X).map a).app q x = ((MonoidalClosed.pre a).app Y).app q y

theorem CellSquare.id {X : SSet.{u}} {q : SimplexCategoryᵒᵖ}
    (x : ((ihom X).obj X).obj q) : CellSquare (𝟙 X) x x := by
  have h := congrFun (congrArg
    (fun f : (ihom X).obj X ⟶ (ihom X).obj X ↦ f.app q) ((ihom X).map_id X)) x
  simpa only [CellSquare, MonoidalClosed.pre_id, NatTrans.id_app] using h

theorem CellSquare.comp {X Y Z : SSet.{u}} {a : X ⟶ Y} {b : Y ⟶ Z}
    {q : SimplexCategoryᵒᵖ} {x : ((ihom X).obj X).obj q}
    {y : ((ihom Y).obj Y).obj q} {z : ((ihom Z).obj Z).obj q}
    (hxy : CellSquare a x y) (hyz : CellSquare b y z) : CellSquare (a ≫ b) x z := by
  change ((ihom X).map (a ≫ b)).app q x = ((MonoidalClosed.pre (a ≫ b)).app Z).app q z
  calc
    ((ihom X).map (a ≫ b)).app q x =
        ((ihom X).map b).app q (((ihom X).map a).app q x) := by
      rw [Functor.map_comp]
      rfl
    _ = ((ihom X).map b).app q (((MonoidalClosed.pre a).app Y).app q y) :=
      congrArg (fun t ↦ ((ihom X).map b).app q t) hxy
    _ = ((MonoidalClosed.pre a).app Z).app q (((ihom Y).map b).app q y) := by
      exact (congrFun (congrArg
        (fun f : (ihom Y).obj Y ⟶ (ihom X).obj Z ↦ f.app q)
        ((MonoidalClosed.pre a).naturality b)) y).symm
    _ = ((MonoidalClosed.pre a).app Z).app q (((MonoidalClosed.pre b).app Z).app q z) :=
      congrArg (fun t ↦ ((MonoidalClosed.pre a).app Z).app q t) hyz
    _ = ((MonoidalClosed.pre (a ≫ b)).app Z).app q z := by
      rw [MonoidalClosed.pre_map]
      rfl

end DaggerNativeEndomorphismCellSquares
