import RectangularCellPostSquares

/-! Postcomposition retains the exact chosen global rectangular cell. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial
open DaggerRectangularInverseWitnessData DaggerNativeEndomorphismSimplexMaps
universe u
namespace DaggerRectangularCellLegPost

theorem post_leg {A B X Y Z : SSet.{u}} {n : ℕ}
    (a : A ⟶ B) (b : X ⟶ Z) (v : X ⟶ Y) (c : Y ⟶ Z) (hv : v ≫ c = b)
    (s : ((ihom A).obj X).obj (op ⦋n⦌))
    (t : ((ihom B).obj Z).obj (op ⦋n⦌)) (h : Square a b s t) :
    Square a c (((ihom A).map v).app (op ⦋n⦌) s) t := by
  apply (square_iff_tensor_map _ _ _ _ _).2
  rw [simplexHomEquiv_post, Category.assoc, hv]
  exact (square_iff_tensor_map _ _ _ _ _).1 h

end DaggerRectangularCellLegPost
