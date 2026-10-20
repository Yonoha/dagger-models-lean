import NativeOriginalCotensorFunctor
import OriginalCoherentCotensorResolution

/-! Whole cotensor-resolution comparison, natural in every original enriched functor. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial DaggerModels OrdinaryRigidification
open DaggerNativeCoherentCotensorConstants DaggerOriginalCoherentCotensorResolution
open DaggerNativeBisimplicialDiagonal
universe u
namespace DaggerNativeCoherentCotensorResolutionNaturality
noncomputable section

/-- Every original object-changing functor acts on the entire parameter diagram. -/
def parameterMap {C D : SimplicialCat.{u, u}} (F : C ⟶ D) :
    parameterDiagram C ⟶ parameterDiagram D where
  app n := DaggerNativeOriginalCotensorFunctor.map (SSet.stdSimplex.obj n.unop) F
  naturality _ _ a :=
    (DaggerNativeOriginalCotensorFunctor.restriction_natural
      (SSet.stdSimplex.map a.unop) F).symm

/-- Postcomposition on the same original coherent nerve in every parameter degree. -/
def resolutionMap {C D : SimplicialCat.{u, u}} (F : C ⟶ D) :
    resolution C ⟶ resolution D where
  app n := coherentNerve.map
    (DaggerNativeOriginalCotensorFunctor.map (SSet.stdSimplex.obj n.unop) F)
  naturality _ _ a := by
    change coherentNerve.map _ ≫ coherentNerve.map _ =
      coherentNerve.map _ ≫ coherentNerve.map _
    rw [← coherentNerve.map_comp, ← coherentNerve.map_comp]
    exact congrArg coherentNerve.map
      (DaggerNativeOriginalCotensorFunctor.restriction_natural
        (SSet.stdSimplex.map a.unop) F).symm

/-- The full comparison square commutes for all enriched functors. -/
theorem comparison_naturality {C D : SimplicialCat.{u, u}} (F : C ⟶ D) :
    coherentNerve.map F ≫ comparison D =
      comparison C ≫ diagonalFunctor.map (resolutionMap F) := by
  apply NatTrans.ext
  funext n x
  have h := congrArg coherentNerve.map
    (DaggerNativeOriginalCotensorFunctor.constant_natural (SSet.stdSimplex.obj n.unop) F)
  rw [coherentNerve.map_comp, coherentNerve.map_comp] at h
  exact congrFun (NatTrans.congr_app h.symm n) x

/-- The same square retains the actual original object function at every vertex. -/
theorem comparison_vertex_naturality {C D : SimplicialCat.{u, u}} (F : C ⟶ D)
    (x : (coherentNerve.obj C).obj (op ⦋0⦌)) :
    NerveVertices.vertexEquiv
      (DaggerOriginalCotensorPrecompositionWeak.originalCotensor (SSet.stdSimplex.obj ⦋0⦌) D)
      ((diagonalFunctor.map (resolutionMap F)).app (op ⦋0⦌)
        ((comparison C).app (op ⦋0⦌) x)) = F.obj (NerveVertices.vertexEquiv C x) := by
  have h := congrFun (NatTrans.congr_app (comparison_naturality F) (op ⦋0⦌)) x
  change NerveVertices.vertexEquiv _
    (((comparison C) ≫ diagonalFunctor.map (resolutionMap F)).app (op ⦋0⦌) x) = _
  rw [← h]
  change NerveVertices.vertexEquiv _
    ((comparison D).app (op ⦋0⦌) ((coherentNerve.map F).app (op ⦋0⦌) x)) = _
  exact (comparison_vertex D ((coherentNerve.map F).app (op ⦋0⦌) x)).trans
    (DaggerNativeGroupoidalCoherentNerveWeak.vertex_map F x)

end
end DaggerNativeCoherentCotensorResolutionNaturality
