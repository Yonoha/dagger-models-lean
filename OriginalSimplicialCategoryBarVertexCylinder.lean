import OriginalSimplicialCategoryBarVertexArrow

/-!
# The original diagonal bar cylinder of precomposition

The native walking-arrow diagram from ab to b is pulled back along each
simplex of the interval. All original simplicial operators are retained.
-/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial DaggerModels
open scoped MonoidalCategory
open DaggerOriginalSimplicialDegreeCategory
open DaggerOriginalSimplicialCategoryOverDiagram
open DaggerOriginalSimplicialCategoryBarConstruction
open DaggerOriginalSimplicialCategoryVertexComposition
open DaggerOriginalSimplicialCategoryBarVertexArrow
universe u
namespace DaggerOriginalSimplicialCategoryBarVertexCylinder
noncomputable section

/-- The literal original over-category chain selected by the original interval simplex. -/
def barVertexCylinderDegree (C : SimplicialCat.{u, u}) {x y : C.Obj}
    (a : (C.enriched.Hom x y).obj (op ⦋0⦌)) (z : C.Obj) (n : SimplexCategoryᵒᵖ)
    (p : (C.enriched.Hom y z).obj n × Δ[1].obj n) : (barComponent C z).obj n :=
  (SimplexCategory.toCat.map (SSet.stdSimplex.objEquiv p.2)).toFunctor ⋙
    vertexOverDiagram C a z n p.1

/-- The original bar cylinder commutes with every original simplicial operator. -/
theorem barVertexCylinderDegree_map (C : SimplicialCat.{u, u}) {x y : C.Obj}
    (a : (C.enriched.Hom x y).obj (op ⦋0⦌)) (z : C.Obj)
    {n m : SimplexCategoryᵒᵖ} (i : n ⟶ m)
    (p : (C.enriched.Hom y z).obj n × Δ[1].obj n) :
    barVertexCylinderDegree C a z m ((C.enriched.Hom y z).map i p.1, Δ[1].map i p.2) =
      (barComponent C z).map i (barVertexCylinderDegree C a z n p) := by
  unfold barVertexCylinderDegree
  rw [vertexOverDiagram_map]
  rfl

/-- The cylinder is a simplicial map on the whole original Hom object. -/
def barVertexCylinderMap (C : SimplicialCat.{u, u}) {x y : C.Obj}
    (a : (C.enriched.Hom x y).obj (op ⦋0⦌)) (z : C.Obj) :
    C.enriched.Hom y z ⊗ Δ[1] ⟶ barComponent C z where
  app n := barVertexCylinderDegree C a z n
  naturality _ _ i := by
    funext p
    exact barVertexCylinderDegree_map C a z i p

end
end DaggerOriginalSimplicialCategoryBarVertexCylinder
