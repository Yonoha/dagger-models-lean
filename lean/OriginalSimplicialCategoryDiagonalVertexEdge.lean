import OriginalSimplicialCategoryBarVertexHomotopy

/-!
# The original vertex edge in the original diagonal nerve

An original Hom vertex gives the degreewise original walking-arrow diagram.
This assembles into its original interval map to the diagonal nerve.
-/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial DaggerModels
open scoped MonoidalCategory
open DaggerOriginalSimplicialDegreeCategory
open DaggerOriginalSimplicialCategoryDiagonalNerve
open DaggerOriginalSimplicialCategoryVertexComposition
universe u
namespace DaggerOriginalSimplicialCategoryDiagonalVertexEdge
noncomputable section

/-- The native walking-arrow diagram of the exact original Hom vertex in every degree. -/
def vertexDegreeDiagram (C : SimplicialCat.{u, u}) {x y : C.Obj}
    (a : (C.enriched.Hom x y).obj (op ⦋0⦌)) (n : SimplexCategoryᵒᵖ) :
    Fin 2 ⥤ degreeObjects C n :=
  ComposableArrows.mk₁ (C := degreeObjects C n) ((vertexPoint C a).app n PUnit.unit)

/-- Original degree operators preserve the same original vertex diagram. -/
theorem vertexDegreeDiagram_map (C : SimplicialCat.{u, u}) {x y : C.Obj}
    (a : (C.enriched.Hom x y).obj (op ⦋0⦌))
    {n m : SimplexCategoryᵒᵖ} (i : n ⟶ m) :
    vertexDegreeDiagram C a m = vertexDegreeDiagram C a n ⋙ degreeMap C i := by
  refine Functor.hext (fun k ↦ ?_) ?_
  · fin_cases k <;> rfl
  · intro k l f
    fin_cases k <;> fin_cases l
    · simp [vertexDegreeDiagram, ComposableArrows.mk₁, ComposableArrows.Mk₁.obj,
        ComposableArrows.Mk₁.map]
      rfl
    · have hp := congrFun ((vertexPoint C a).naturality i) PUnit.unit
      change (vertexPoint C a).app m PUnit.unit =
        (C.enriched.Hom x y).map i ((vertexPoint C a).app n PUnit.unit) at hp
      simpa [vertexDegreeDiagram, ComposableArrows.mk₁, ComposableArrows.Mk₁.obj,
        ComposableArrows.Mk₁.map] using heq_of_eq hp
    · have ht : (1 : Fin 2) ≤ 0 := leOfHom f
      norm_num at ht
    · simp [vertexDegreeDiagram, ComposableArrows.mk₁, ComposableArrows.Mk₁.obj,
        ComposableArrows.Mk₁.map]
      rfl

/-- The original Hom vertex gives its actual simplicial edge in the original diagonal nerve. -/
def diagonalVertexEdge (C : SimplicialCat.{u, u}) {x y : C.Obj}
    (a : (C.enriched.Hom x y).obj (op ⦋0⦌)) : Δ[1] ⟶ diagonalNerveFunctor.obj C where
  app n t := (SimplexCategory.toCat.map (SSet.stdSimplex.objEquiv t)).toFunctor ⋙
    vertexDegreeDiagram C a n
  naturality _ _ i := by
    funext t
    rw [vertexDegreeDiagram_map C a i]
    rfl

end
end DaggerOriginalSimplicialCategoryDiagonalVertexEdge
