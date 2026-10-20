import NativeEndomorphismSimplexMaps

/-!
# Every simplex operator preserves strict endomorphism-cell squares

At vertices the strict cell square is exactly the original endomorphism square.
Both statements retain the actual native internal Hom and all original maps.
-/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial
open DaggerNativeEndomorphismCellSquares DaggerNativeIhomHoObjects
open DaggerNativeWalkingRetractionMappingEquivalence
universe u
namespace DaggerEndomorphismCellOperators

theorem restrict_square {X Y : SSet.{u}} {a : X ⟶ Y}
    {q q' : SimplexCategoryᵒᵖ} (α : q' ⟶ q)
    {x : ((ihom X).obj X).obj q'} {y : ((ihom Y).obj Y).obj q'}
    (h : DaggerNativeEndomorphismCellSquares.CellSquare a x y) :
    DaggerNativeEndomorphismCellSquares.CellSquare a
      (((ihom X).obj X).map α x) (((ihom Y).obj Y).map α y) := by
  change ((ihom X).map a).app q (((ihom X).obj X).map α x) =
    ((MonoidalClosed.pre a).app Y).app q (((ihom Y).obj Y).map α y)
  calc
    ((ihom X).map a).app q (((ihom X).obj X).map α x) =
        ((ihom X).obj Y).map α (((ihom X).map a).app q' x) :=
      congrFun (((ihom X).map a).naturality α) x
    _ = ((ihom X).obj Y).map α (((MonoidalClosed.pre a).app Y).app q' y) :=
      congrArg (fun t ↦ ((ihom X).obj Y).map α t) h
    _ = ((MonoidalClosed.pre a).app Y).app q (((ihom Y).obj Y).map α y) :=
      (congrFun (((MonoidalClosed.pre a).app Y).naturality α) y).symm

def vertex {X : SSet.{u}} (h : X ⟶ X) : ((ihom X).obj X).obj (op ⦋0⦌) :=
  SSet.hoFunctor.obj.equiv _ (homObject h)

theorem vertex_square_iff {X Y : SSet.{u}} (a : X ⟶ Y) (h : X ⟶ X) (k : Y ⟶ Y) :
    DaggerNativeEndomorphismCellSquares.CellSquare a (vertex h) (vertex k) ↔ h ≫ a = a ≫ k := by
  have he : homObject (h ≫ a) = homObject (a ≫ k) ↔ h ≫ a = a ≫ k :=
    (homObjectEquiv X Y).injective.eq_iff
  rw [← he]
  constructor
  · intro hs
    apply (SSet.hoFunctor.obj.equiv _).injective
    rw [← post_obj h a, ← pre_obj a k, postHoFunctor, preHoFunctor, ho_map_obj, ho_map_obj]
    exact hs
  · intro hs
    have hv := congrArg (SSet.hoFunctor.obj.equiv ((ihom X).obj Y)) hs
    rw [← post_obj h a, ← pre_obj a k, postHoFunctor, preHoFunctor, ho_map_obj, ho_map_obj] at hv
    exact hv

end DaggerEndomorphismCellOperators
