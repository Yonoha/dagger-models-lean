import SimplexInverseWitnessCategory
import NativeEndomorphismSimplexMaps

/-!
# Partial inverse data between two original arrow stages

The inverse crosses from the earlier codomain to the later domain. Both pairs
of triangles are in the actual rectangular internal Homs. Neither stage arrow
is asserted weak by these partial data alone.
-/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial MonoidalCategory
open DaggerNativeHoIsoTriangles DaggerNativeIhomHoObjects
open DaggerNativeEndomorphismSimplexMaps
universe u v w
namespace DaggerRectangularInverseWitnessData
noncomputable section

def Square {A B A' B' : SSet.{u}} (a : A ⟶ A') (b : B ⟶ B') {n : ℕ}
    (s : ((ihom A).obj B).obj (op ⦋n⦌)) (t : ((ihom A').obj B').obj (op ⦋n⦌)) : Prop :=
  ((ihom A).map b).app (op ⦋n⦌) s =
    ((MonoidalClosed.pre a).app B').app (op ⦋n⦌) t

theorem square_iff_tensor_map {A B A' B' : SSet.{u}} (a : A ⟶ A') (b : B ⟶ B') (n : ℕ)
    (s : ((ihom A).obj B).obj (op ⦋n⦌)) (t : ((ihom A').obj B').obj (op ⦋n⦌)) :
    Square a b s t ↔ simplexHomEquiv A B n s ≫ b =
      a ▷ Δ[n] ≫ simplexHomEquiv A' B' n t := by
  constructor
  · intro h
    have hh := congrArg (simplexHomEquiv A B' n) h
    simpa only [simplexHomEquiv_post, simplexHomEquiv_pre] using hh
  · intro h
    apply (simplexHomEquiv A B' n).injective
    simpa only [simplexHomEquiv_post, simplexHomEquiv_pre] using h

variable {C : Type w} [Category.{v} C] (R : C ⥤ SSet.{u})

structure Data {a b : Arrow C} (p : a ⟶ b) where
  inv : R.obj a.right ⟶ R.obj b.left
  left : IsoTriangles ((ihom (R.obj a.left)).obj (R.obj b.left))
    (homObject (R.map a.hom ≫ inv)) (homObject (R.map p.left))
  right : IsoTriangles ((ihom (R.obj a.right)).obj (R.obj b.right))
    (homObject (inv ≫ R.map b.hom)) (homObject (R.map p.right))

end
end DaggerRectangularInverseWitnessData
