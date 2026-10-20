import OriginalSimplicialCategoryDiagonalVertexEdge
import OriginalSimplicialCategoryWholeBarVertexHomotopy

/-!
# The original bar cylinder projects to precisely the original vertex edge

On every original Hom simplex, projection of the actual original bar cylinder
is the same original diagonal-nerve edge. Its base path is independent of the
original endpoint and the original Hom simplex.
-/
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite Simplicial DaggerModels
open scoped MonoidalCategory
open DaggerOriginalSimplicialDegreeCategory
open DaggerOriginalSimplicialCategoryDiagonalNerve
open DaggerOriginalSimplicialCategoryOverDiagram
open DaggerOriginalSimplicialCategoryBarConstruction
open DaggerOriginalSimplicialCategoryBarCoproductDegrees
open DaggerOriginalSimplicialCategoryWholeBarFibreIso
open DaggerOriginalSimplicialCategoryBarVertexArrow
open DaggerOriginalSimplicialCategoryBarVertexCylinder
open DaggerOriginalSimplicialCategoryDiagonalVertexEdge
open DaggerOriginalSimplicialCategoryWholeBarVertexHomotopy
universe u
namespace DaggerOriginalSimplicialCategoryBarVertexProjection
noncomputable section

/-- Each original component cylinder projects to the exact original vertex edge. -/
theorem barVertexCylinderMap_projection (C : SimplicialCat.{u, u}) {x y : C.Obj}
    (a : (C.enriched.Hom x y).obj (op ⦋0⦌)) (z : C.Obj) :
    barVertexCylinderMap C a z ≫ barComponentProjection C z =
      CartesianMonoidalCategory.snd (C.enriched.Hom y z) Δ[1] ≫ diagonalVertexEdge C a := by
  apply NatTrans.ext
  funext n p
  change ((SimplexCategory.toCat.map (SSet.stdSimplex.objEquiv p.2)).toFunctor ⋙
      vertexOverDiagram C a z n p.1) ⋙ Over.forget (T := degreeObjects C n) z =
    (SimplexCategory.toCat.map (SSet.stdSimplex.objEquiv p.2)).toFunctor ⋙
      vertexDegreeDiagram C a n
  rw [Functor.assoc, vertexOverDiagram_forget]
  rfl

/-- The entire original cylinder retains the same original vertex edge under projection. -/
theorem wholeBarVertexCylinderMap_projection (C : SimplicialCat.{u, u}) {x y : C.Obj}
    (a : (C.enriched.Hom x y).obj (op ⦋0⦌)) :
    wholeBarVertexCylinderMap C a ≫ barProjection C =
      CartesianMonoidalCategory.snd (originalHomSum C y) Δ[1] ≫ diagonalVertexEdge C a := by
  apply NatTrans.ext
  funext n p
  rcases p with ⟨b, t⟩
  obtain ⟨⟨z, b⟩, rfl⟩ := (coproductDegreeEquiv (C.enriched.Hom y) n).surjective b
  change (barProjection C).app n ((wholeBarVertexCylinderMap C a).app n
      (coproductDegreeEquiv (C.enriched.Hom y) n ⟨z, b⟩, t)) =
    (diagonalVertexEdge C a).app n t
  rw [wholeBarVertexCylinderMap_apply, barDegreeEquiv_projection]
  exact congrFun (NatTrans.congr_app (barVertexCylinderMap_projection C a z) n) (b, t)

end
end DaggerOriginalSimplicialCategoryBarVertexProjection
