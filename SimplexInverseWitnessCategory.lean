import NativeEndomorphismCellSquares
import NativeJoyalWeakSimplexInverse

/-!
# The category of whole simplex-inverse witnesses over original arrows

Morphisms preserve the actual inverse map and every chosen edge and triangle.
They are original arrow squares, with strict coherence under the whole functor R.
The projection is faithful. No accessibility premise or conclusion is added here.
-/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial
open DaggerNativeHoIsoTriangles DaggerNativeJoyalWeakSimplexInverse
open DaggerNativeEndomorphismCellSquares
universe u v w
namespace DaggerSimplexInverseWitnessCategory
noncomputable section

structure TriangleSquare {X Y : SSet.{u}} (a : X ⟶ Y)
    {x₀ x₁ : SSet.hoFunctor.obj ((ihom X).obj X)}
    {y₀ y₁ : SSet.hoFunctor.obj ((ihom Y).obj Y)}
    (d : IsoTriangles ((ihom X).obj X) x₀ x₁)
    (e : IsoTriangles ((ihom Y).obj Y) y₀ y₁) : Prop where
  forward : CellSquare a d.forward.edge e.forward.edge
  backward : CellSquare a d.backward.edge e.backward.edge
  leftTriangle : CellSquare a d.leftTriangle.simplex e.leftTriangle.simplex
  rightTriangle : CellSquare a d.rightTriangle.simplex e.rightTriangle.simplex

theorem TriangleSquare.id {X : SSet.{u}}
    {x₀ x₁ : SSet.hoFunctor.obj ((ihom X).obj X)}
    (d : IsoTriangles ((ihom X).obj X) x₀ x₁) : TriangleSquare (𝟙 X) d d :=
  ⟨CellSquare.id _, CellSquare.id _, CellSquare.id _, CellSquare.id _⟩

theorem TriangleSquare.comp {X Y Z : SSet.{u}} {a : X ⟶ Y} {b : Y ⟶ Z}
    {x₀ x₁ : SSet.hoFunctor.obj ((ihom X).obj X)}
    {y₀ y₁ : SSet.hoFunctor.obj ((ihom Y).obj Y)}
    {z₀ z₁ : SSet.hoFunctor.obj ((ihom Z).obj Z)}
    {d : IsoTriangles ((ihom X).obj X) x₀ x₁}
    {e : IsoTriangles ((ihom Y).obj Y) y₀ y₁}
    {f : IsoTriangles ((ihom Z).obj Z) z₀ z₁}
    (h : TriangleSquare a d e) (k : TriangleSquare b e f) : TriangleSquare (a ≫ b) d f :=
  ⟨h.forward.comp k.forward, h.backward.comp k.backward,
    h.leftTriangle.comp k.leftTriangle, h.rightTriangle.comp k.rightTriangle⟩

variable {C : Type w} [Category.{v} C] (R : C ⥤ SSet.{u})

structure Witness where
  arrow : Arrow C
  data : SimplexInverseData (R.map arrow.hom)

structure Hom (X Y : Witness R) where
  square : X.arrow ⟶ Y.arrow
  inverse_commutes : R.map square.right ≫ Y.data.inv = X.data.inv ≫ R.map square.left
  triangleLeft : TriangleSquare (R.map square.left) X.data.left Y.data.left
  triangleRight : TriangleSquare (R.map square.right) X.data.right Y.data.right

@[ext]
theorem Hom.ext {X Y : Witness R} {f g : Hom R X Y} (h : f.square = g.square) : f = g := by
  cases f
  cases g
  cases h
  rfl

instance category : Category (Witness R) where
  Hom := Hom R
  id X :=
    { square := 𝟙 X.arrow
      inverse_commutes := by
        rw [Arrow.id_right, Arrow.id_left, R.map_id X.arrow.right, R.map_id X.arrow.left]
        exact (Category.id_comp X.data.inv).trans (Category.comp_id X.data.inv).symm
      triangleLeft := by
        rw [Arrow.id_left, R.map_id X.arrow.left]
        exact TriangleSquare.id X.data.left
      triangleRight := by
        rw [Arrow.id_right, R.map_id X.arrow.right]
        exact TriangleSquare.id X.data.right }
  comp {X Y Z} f g :=
    { square := f.square ≫ g.square
      inverse_commutes := by
        simp only [Arrow.comp_right, Arrow.comp_left, Functor.map_comp]
        rw [Category.assoc, g.inverse_commutes, ← Category.assoc,
          f.inverse_commutes, Category.assoc]
      triangleLeft := by
        simpa only [Arrow.comp_left, Functor.map_comp] using
          f.triangleLeft.comp g.triangleLeft
      triangleRight := by
        simpa only [Arrow.comp_right, Functor.map_comp] using
          f.triangleRight.comp g.triangleRight }
  id_comp f := Hom.ext R (Category.id_comp f.square)
  comp_id f := Hom.ext R (Category.comp_id f.square)
  assoc f g h := Hom.ext R (Category.assoc f.square g.square h.square)

def forget : Witness R ⥤ Arrow C where
  obj X := X.arrow
  map f := f.square

instance forgetFaithful : (forget R).Faithful where
  map_injective h := Hom.ext R h

end
end DaggerSimplexInverseWitnessCategory
