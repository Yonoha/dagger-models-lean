import NativeDegreeCotensorComparison
import NativeCoherentCotensorResolutionNaturality

/-! Original nerve comparison: every functor and vertex, before any weakness claim. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial DaggerModels OrdinaryRigidification
open DaggerOriginalSimplicialDegreeCategory DaggerActualConstantEnrichmentFunctor
open DaggerNativeDegreeCotensorYoneda DaggerNativeDegreeCotensorComparison
open DaggerOriginalCoherentCotensorResolution DaggerOriginalSimplicialCategoryDiagonalNerve
open DaggerNativeCoherentCotensorResolutionNaturality DaggerNativeBisimplicialDiagonal
universe u
namespace DaggerNativeDegreeCotensorDiagonal
noncomputable section

/-- The whole bisimplicial square commutes for every original enriched functor. -/
theorem comparison_naturality {C D : SimplicialCat.{u, u}} (F : C ⟶ D) :
    bisimplicialNerveFunctor.map F ≫ DaggerNativeDegreeCotensorComparison.comparison D =
      DaggerNativeDegreeCotensorComparison.comparison C ≫ resolutionMap F := by
  apply NatTrans.ext
  funext n
  change nerveMap (degreeFunctor F n) ≫ (_ ≫ _) = (_ ≫ _) ≫ coherentNerve.map _
  rw [← Category.assoc, ← inverse_naturality (degreeFunctor F n), Category.assoc,
    ← coherentNerve.map_comp, functor_naturality, coherentNerve.map_comp, Category.assoc]

/-- The exact degree-zero simplex retains its SAME original vertex. -/
theorem comparison_vertex (C : SimplicialCat.{u, u})
    (p : (nerve (degreeObjects C (op ⦋0⦌))).obj (op ⦋0⦌)) :
    NerveVertices.vertexEquiv
      (DaggerOriginalCotensorPrecompositionWeak.originalCotensor (SSet.stdSimplex.obj ⦋0⦌) C)
      (((DaggerNativeDegreeCotensorComparison.comparison C).app (op ⦋0⦌)).app (op ⦋0⦌) p) =
        p.obj 0 :=
  DaggerNativeGroupoidalCoherentNerveWeak.vertex_map (degreeToCotensor C ⦋0⦌)
    ((DaggerActualConstantCoherentNerve.coherentNerveIso
      (degreeObjects C (op ⦋0⦌))).inv.app (op ⦋0⦌) p)

/-- The original ordinary diagonal nerve maps to the same cotensor-resolution diagonal. -/
def diagonalComparison (C : SimplicialCat.{u, u}) :
    diagonalNerveFunctor.obj C ⟶ diagonalFunctor.obj (resolution C) :=
  diagonalFunctor.map (DaggerNativeDegreeCotensorComparison.comparison C)

/-- All original functor maps are retained by the full diagonal comparison. -/
theorem diagonalComparison_naturality {C D : SimplicialCat.{u, u}} (F : C ⟶ D) :
    diagonalNerveFunctor.map F ≫ diagonalComparison D =
      diagonalComparison C ≫ diagonalFunctor.map (resolutionMap F) := by
  have h := congrArg diagonalFunctor.map (comparison_naturality F)
  simpa only [CategoryTheory.Functor.map_comp] using h

/-- The diagonal comparison retains every original vertex, with no distinctness condition. -/
theorem diagonalComparison_vertex (C : SimplicialCat.{u, u})
    (p : (diagonalNerveFunctor.obj C).obj (op ⦋0⦌)) :
    NerveVertices.vertexEquiv
      (DaggerOriginalCotensorPrecompositionWeak.originalCotensor (SSet.stdSimplex.obj ⦋0⦌) C)
      ((diagonalComparison C).app (op ⦋0⦌) p) = p.obj 0 := comparison_vertex C p

end
end DaggerNativeDegreeCotensorDiagonal
