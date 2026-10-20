import OriginalSimplicialCategoryBarVertexProjection

/-!
# The actual strict-fibre transport has its original geometric bar cylinder

Precompose the original whole Hom cylinder by the proved Hom-fibre isomorphism.
Its endpoints are precisely the specified original strict-fibre transport
followed by inclusion and the original source-fibre inclusion. Its projection
is the original vertex edge, independent of the original fibre simplex.
This does not assert a homotopy-fibre comparison or a quasifibration theorem.
-/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial DaggerModels
open scoped MonoidalCategory
open DaggerOriginalSimplicialCategoryBarConstruction
open DaggerOriginalSimplicialCategoryWholeBarFibreDegree
open DaggerOriginalSimplicialCategoryWholeBarFibreIso
open DaggerOriginalSimplicialCategoryWholeBarFibreTransport
open DaggerOriginalSimplicialCategoryWholeBarVertexHomotopy
open DaggerOriginalSimplicialCategoryDiagonalVertexEdge
open DaggerOriginalSimplicialCategoryBarVertexProjection
universe u
namespace DaggerOriginalSimplicialCategoryWholeBarFibreVertexHomotopy
noncomputable section

/-- The specified whole strict-fibre transport has its actual homotopy in the original bar. -/
def wholeBarFibreVertexHomotopy (C : SimplicialCat.{u, u}) {x y : C.Obj}
    (a : (C.enriched.Hom x y).obj (op ⦋0⦌)) :
    SSet.Homotopy (wholeBarFibreTransport C a ≫ (wholeBarFibre C x).ι)
      (wholeBarFibre C y).ι := by
  refine SSet.Homotopy.congr
    ((wholeBarVertexHomotopy C a).precomp (wholeBarHomFibreIso C y).inv) ?_ ?_
  · simp only [wholeBarFibreTransport, Category.assoc, wholeBarHomFibreIso_hom_ι]
  · rw [← wholeBarHomFibreIso_hom_ι, Iso.inv_hom_id_assoc]

/-- The entire strict-fibre cylinder projects to precisely the same original base edge. -/
theorem wholeBarFibreVertexHomotopy_projection (C : SimplicialCat.{u, u}) {x y : C.Obj}
    (a : (C.enriched.Hom x y).obj (op ⦋0⦌)) :
    (wholeBarFibreVertexHomotopy C a).h ≫ barProjection C =
      CartesianMonoidalCategory.snd (wholeBarFibre C y).toSSet Δ[1] ≫
        diagonalVertexEdge C a := by
  apply NatTrans.ext
  funext n p
  change (barProjection C).app n ((wholeBarVertexCylinderMap C a).app n
      ((wholeBarHomFibreIso C y).inv.app n p.1, p.2)) =
    (diagonalVertexEdge C a).app n p.2
  exact congrFun (NatTrans.congr_app (wholeBarVertexCylinderMap_projection C a) n)
    ((wholeBarHomFibreIso C y).inv.app n p.1, p.2)

end
end DaggerOriginalSimplicialCategoryWholeBarFibreVertexHomotopy
