import Mathlib.AlgebraicTopology.SimplicialSet.Op
import Mathlib.AlgebraicTopology.SimplicialSet.Skeleton

/-! Part I `dj.not.adjunctions`: the common vertices are the actual zero-skeleton. -/
set_option warningAsError false
open CategoryTheory Simplicial Opposite
universe u
namespace DaggerModels.SSetVertices

def obj (A : SSet.{u}) : SSet.{u} :=
  (Functor.const SimplexCategoryᵒᵖ).obj (A.obj (op ⦋0⦌))
def inclusion (A : SSet.{u}) : obj A ⟶ A where
  app n x := A.map (SimplexCategory.const n.unop ⦋0⦌ 0).op x
  naturality {n m} f := by
    funext x
    change A.map (SimplexCategory.const m.unop ⦋0⦌ 0).op x =
      A.map f.unop.op (A.map (SimplexCategory.const n.unop ⦋0⦌ 0).op x)
    rw [← FunctorToTypes.map_comp_apply, ← op_comp]
    rw [SimplexCategory.eq_const_to_zero (f.unop ≫ SimplexCategory.const n.unop ⦋0⦌ 0)]

theorem mono_inclusion (A : SSet.{u}) : Mono (inclusion A) := by sorry
-- Mathlib's skeleton n uses nondegenerate dimensions strictly below n.
theorem range_inclusion (A : SSet.{u}) :
    SSet.Subcomplex.range (inclusion A) = A.skeleton 1 := by sorry
theorem exists_skeletonIso (A : SSet.{u}) :
    ∃ e : obj A ≅ (A.skeleton 1).toSSet, e.hom ≫ (A.skeleton 1).ι = inclusion A := by sorry

end DaggerModels.SSetVertices
