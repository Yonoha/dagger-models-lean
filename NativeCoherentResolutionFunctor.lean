import NativeCoherentCotensorResolutionNaturality
import NativeDegreeCotensorDiagonal

/-! Bundle the SAME original coherent cotensor resolution and both whole natural comparisons. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial DaggerModels OrdinaryRigidification
open DaggerOriginalCoherentCotensorResolution DaggerNativeBisimplicialDiagonal
open DaggerNativeCoherentCotensorResolutionNaturality
open DaggerOriginalSimplicialCategoryDiagonalNerve
universe u
namespace DaggerNativeCoherentResolutionFunctor
noncomputable section

/-- Original identity maps induce the entire identity of the original resolution. -/
theorem resolutionMap_id (C : SimplicialCat.{u, u}) : resolutionMap (𝟙 C) = 𝟙 (resolution C) := by
  apply NatTrans.ext
  funext q
  change coherentNerve.map
    (DaggerNativeOriginalCotensorFunctor.map (SSet.stdSimplex.obj q.unop) (𝟙 C)) = 𝟙 _
  rw [DaggerNativeOriginalCotensorFunctor.map_id, coherentNerve.map_id]

/-- Composition retains each original enriched Hom map and object function. -/
theorem resolutionMap_comp {C D E : SimplicialCat.{u, u}} (F : C ⟶ D) (G : D ⟶ E) :
    resolutionMap (F ≫ G) = resolutionMap F ≫ resolutionMap G := by
  apply NatTrans.ext
  funext q
  change coherentNerve.map
    (DaggerNativeOriginalCotensorFunctor.map (SSet.stdSimplex.obj q.unop) (F ≫ G)) =
      coherentNerve.map (DaggerNativeOriginalCotensorFunctor.map
        (SSet.stdSimplex.obj q.unop) F) ≫ coherentNerve.map
          (DaggerNativeOriginalCotensorFunctor.map (SSet.stdSimplex.obj q.unop) G)
  rw [DaggerNativeOriginalCotensorFunctor.map_comp, coherentNerve.map_comp]

/-- The SAME original resolution, on all original simplicial categories and functors. -/
def resolutionFunctor : SimplicialCat.{u, u} ⥤ SimplexCategoryᵒᵖ ⥤ SSet.{u} where
  obj := resolution
  map := resolutionMap
  map_id := resolutionMap_id
  map_comp := resolutionMap_comp

/-- Take the original diagonal without changing the resolution or its maps. -/
def diagonalResolutionFunctor : SimplicialCat.{u, u} ⥤ SSet.{u} :=
  resolutionFunctor ⋙ diagonalFunctor

/-- The original coherent comparison as a WHOLE natural transformation. -/
def coherentComparison : coherentNerve ⟶ diagonalResolutionFunctor.{u} where
  app := DaggerOriginalCoherentCotensorResolution.comparison
  naturality _ _ F := DaggerNativeCoherentCotensorResolutionNaturality.comparison_naturality F

/-- The original ordinary diagonal comparison as a WHOLE natural transformation. -/
def ordinaryComparison : diagonalNerveFunctor ⟶ diagonalResolutionFunctor.{u} where
  app := DaggerNativeDegreeCotensorDiagonal.diagonalComparison
  naturality _ _ F := DaggerNativeDegreeCotensorDiagonal.diagonalComparison_naturality F

end
end DaggerNativeCoherentResolutionFunctor
