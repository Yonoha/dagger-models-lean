import OriginalFullVertexSubcomplexKan

/-!
# Universal property of a full vertex subcomplex

A map into a simplicial set factors through its full vertex subcomplex
exactly when every source vertex lands in the chosen vertex set. This is the
pointwise factorization mechanism needed for strict-endpoint path simplices.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial

universe u

namespace DaggerOriginalFullVertexSubcomplex

noncomputable section

theorem range_le_fullVertexSubcomplex_iff {Y X : SSet.{u}}
    (V : Set (X.obj (op ⦋0⦌))) (f : Y ⟶ X) :
    SSet.Subcomplex.range f ≤ fullVertexSubcomplex X V ↔
      ∀ y : Y.obj (op ⦋0⦌), f.app (op ⦋0⦌) y ∈ V := by
  constructor
  · intro hf y
    have hy : f.app (op ⦋0⦌) y ∈
        (fullVertexSubcomplex X V).obj (op ⦋0⦌) := hf _ ⟨y, rfl⟩
    have hvertex := hy (𝟙 ⦋0⦌)
    simpa only [op_id, FunctorToTypes.map_id_apply] using hvertex
  · intro hv m s hs
    obtain ⟨a, rfl⟩ := hs
    change ∀ v : ⦋0⦌ ⟶ m.unop, X.map v.op (f.app m a) ∈ V
    intro v
    have hn := congrFun (f.naturality v.op) a
    change f.app (op ⦋0⦌) (Y.map v.op a) =
      X.map v.op (f.app m a) at hn
    rw [← hn]
    exact hv _

/-- The unique factorization through the full vertex subcomplex. -/
def liftMapOfVertices {Y X : SSet.{u}} (V : Set (X.obj (op ⦋0⦌)))
    (f : Y ⟶ X)
    (hvertex : ∀ y : Y.obj (op ⦋0⦌), f.app (op ⦋0⦌) y ∈ V) :
    Y ⟶ (fullVertexSubcomplex X V : SSet) :=
  SSet.Subcomplex.lift f ((range_le_fullVertexSubcomplex_iff V f).2 hvertex)

@[reassoc (attr := simp)]
theorem liftMapOfVertices_ι {Y X : SSet.{u}}
    (V : Set (X.obj (op ⦋0⦌))) (f : Y ⟶ X)
    (hvertex : ∀ y : Y.obj (op ⦋0⦌), f.app (op ⦋0⦌) y ∈ V) :
    liftMapOfVertices V f hvertex ≫ (fullVertexSubcomplex X V).ι = f :=
  SSet.Subcomplex.lift_ι f _

theorem liftMapOfVertices_unique {Y X : SSet.{u}}
    (V : Set (X.obj (op ⦋0⦌))) (f : Y ⟶ X)
    (hvertex : ∀ y : Y.obj (op ⦋0⦌), f.app (op ⦋0⦌) y ∈ V)
    (g : Y ⟶ (fullVertexSubcomplex X V : SSet))
    (hg : g ≫ (fullVertexSubcomplex X V).ι = f) :
    g = liftMapOfVertices V f hvertex := by
  apply (cancel_mono (fullVertexSubcomplex X V).ι).mp
  simpa only [liftMapOfVertices_ι] using hg

end

end DaggerOriginalFullVertexSubcomplex
