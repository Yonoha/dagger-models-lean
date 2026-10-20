import OriginalEC2HomotopyFixedPointObject
import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex

/-!
# The full simplicial subset selected by vertices

A simplex belongs to this subcomplex exactly when every vertex belongs to
the selected set. This is independent of any dagger quasi-category or
specific homotopy fixed-point construction.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial

universe u

namespace DaggerOriginalFullVertexSubcomplex

noncomputable section

/-- The full subcomplex of a simplicial set spanned by a set of vertices. -/
def fullVertexSubcomplex (X : SSet.{u}) (V : Set (X.obj (op ⦋0⦌))) :
    X.Subcomplex where
  obj n := {s | ∀ v : ⦋0⦌ ⟶ n.unop, X.map v.op s ∈ V}
  map {a b} f s hs v := by
    have hv := hs (v ≫ f.unop)
    simpa only [op_comp, FunctorToTypes.map_comp_apply] using hv

/-- Membership is determined by all zero-dimensional faces. -/
theorem mem_fullVertexSubcomplex_iff (X : SSet.{u})
    (V : Set (X.obj (op ⦋0⦌))) (n : SimplexCategoryᵒᵖ) (s : X.obj n) :
    s ∈ (fullVertexSubcomplex X V).obj n ↔
      ∀ v : ⦋0⦌ ⟶ n.unop, X.map v.op s ∈ V :=
  Iff.rfl

end

end DaggerOriginalFullVertexSubcomplex
