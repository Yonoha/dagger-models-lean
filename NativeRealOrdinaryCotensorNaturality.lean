import NativeRealOrdinaryCotensorComparison
import NativeRealCotensorComparisonNaturality

/-! The real ordinary comparison is natural for ALL original dagger enriched functors. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial DaggerModels
open DaggerOriginalSimplicialDegreeCategory DaggerNativeDaggerDegreeCotensor
open DaggerNativeDaggerDegreeNerveComparison DaggerNativeRealOrdinaryCotensorComparison
universe u
namespace DaggerNativeRealOrdinaryCotensorNaturality
noncomputable section

/-- Evaluate the SAME original object-changing dagger functor in every degree. -/
def degreeNerveMap {C D : DaggerSimplicialCat.{u, u}} (F : C ⟶ D)
    (n : SimplexCategoryᵒᵖ) : degreeNerve C n ⟶ degreeNerve D n := by
  letI := degreeDaggerCategory C n
  letI := degreeDaggerCategory D n
  refine DaggerNativeOrdinaryDaggerNerveFunctor.map (degreeFunctor F.toEnrichedFunctor n) ?_
  intro x y f
  exact (congrFun (NatTrans.congr_app (F.map_dagger x y) n) f).symm

/-- Its entire parameter diagram map is the old bisimplicial nerve map. -/
def degreeDiagramMap {C D : DaggerSimplicialCat.{u, u}} (F : C ⟶ D) :
    degreeDiagram C ⟶ degreeDiagram D where
  app := degreeNerveMap F
  naturality _ _ a := by
    apply DaggerSSet.Hom.ext
    exact (DaggerOriginalSimplicialCategoryDiagonalNerve.bisimplicialNerveFunctor.map
      F.toEnrichedFunctor).naturality a

/-- No source object or arrow of the original ordinary comparison is discarded. -/
def coefficientMap {C D : DaggerSimplicialCat.{u, u}} (F : C ⟶ D) :
    ordinaryAction C ⟶ ordinaryAction D :=
  DaggerNativeRealDaggerDiagramAction.map (degreeDiagramMap F)

/-- The WHOLE square is natural as strict maps for the unchanged original C2. -/
theorem comparison_naturality {C D : DaggerSimplicialCat.{u, u}} (F : C ⟶ D) :
    DaggerNativeRealOrdinaryCotensorComparison.comparison C ≫
        DaggerNativeRealCotensorComparisonNaturality.coefficientMap F =
      coefficientMap F ≫ DaggerNativeRealOrdinaryCotensorComparison.comparison D := by
  apply Action.hom_ext
  apply NatTrans.ext
  funext n x
  have h := DaggerNativeDegreeCotensorDiagonal.comparison_naturality F.toEnrichedFunctor
  exact (congrFun (NatTrans.congr_app (NatTrans.congr_app h n)
    (DaggerNativeRealEdgewiseIndex.epsilon.op.obj n)) x).symm

end
end DaggerNativeRealOrdinaryCotensorNaturality
