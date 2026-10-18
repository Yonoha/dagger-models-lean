import RectangularCellStageRefinements

/-! Rectangular squares remain strict after actual target postcomposition. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial
open DaggerRectangularInverseWitnessData DaggerNativeEndomorphismSimplexMaps
universe u
namespace DaggerRectangularCellPostSquares

theorem post_target {A B X Y Z : SSet.{u}} {n : ℕ}
    (a : A ⟶ B) (b : X ⟶ Y) (c : Y ⟶ Z)
    (s : ((ihom A).obj X).obj (op ⦋n⦌))
    (t : ((ihom B).obj Y).obj (op ⦋n⦌)) (h : Square a b s t) :
    Square a (b ≫ c) s (((ihom B).map c).app (op ⦋n⦌) t) := by
  apply (square_iff_tensor_map _ _ _ _ _).2
  have ht := congrArg (fun f ↦ f ≫ c) ((square_iff_tensor_map _ _ _ _ _).1 h)
  simpa only [simplexHomEquiv_post, Category.assoc] using ht

end DaggerRectangularCellPostSquares
