import NativeOrdinaryDaggerNerveFunctor
import NativeDegreeCotensorComparison
import NativeDaggerCotensorResolution

/-! The SAME original ordinary/coherent comparison lifts to a diagram of dagger sets. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial DaggerModels OrdinaryRigidification
open DaggerOriginalSimplicialDegreeCategory DaggerOriginalSimplicialDaggerDegreeLaws
open DaggerNativeDaggerDegreeCotensor DaggerNativeOrdinaryDaggerNerveLift
universe u
namespace DaggerNativeDaggerDegreeNerveComparison
noncomputable section

/-- Use the original ordinary degree category with its original evaluated dagger. -/
def degreeNerve (C : DaggerSimplicialCat.{u, u}) (n : SimplexCategoryᵒᵖ) : DaggerSSet.{u} := by
  letI := degreeDaggerCategory C n
  exact daggerNerve (degreeObjects C.toSimplicialCat n)

/-- Every original parameter operator preserves this SAME degree dagger. -/
def parameterMap (C : DaggerSimplicialCat.{u, u})
    {n m : SimplexCategoryᵒᵖ} (a : n ⟶ m) : degreeNerve C n ⟶ degreeNerve C m := by
  letI := degreeDaggerCategory C n
  letI := degreeDaggerCategory C m
  exact DaggerNativeOrdinaryDaggerNerveFunctor.map (degreeMap C.toSimplicialCat a)
    (degreeDagger_naturality C a)

/-- The original bisimplicial ordinary nerve has dagger only in its outer nerve index. -/
def degreeDiagram (C : DaggerSimplicialCat.{u, u}) : SimplexCategoryᵒᵖ ⥤ DaggerSSet.{u} where
  obj := degreeNerve C
  map a := parameterMap C a
  map_id n := by
    apply DaggerSSet.Hom.ext
    exact (DaggerOriginalSimplicialCategoryDiagonalNerve.bisimplicialNerveFunctor.obj
      C.toSimplicialCat).map_id n
  map_comp a b := by
    apply DaggerSSet.Hom.ext
    exact (DaggerOriginalSimplicialCategoryDiagonalNerve.bisimplicialNerveFunctor.obj
      C.toSimplicialCat).map_comp a b

/-- The OLD constant-nerve inverse and OLD Yoneda map, now with their original daggers. -/
def comparisonApp (C : DaggerSimplicialCat.{u, u}) (n : SimplexCategoryᵒᵖ) :
    degreeNerve C n ⟶ (DaggerNativeDaggerCotensorResolution.resolution C).obj n := by
  letI := degreeDaggerCategory C n
  exact inverse (degreeObjects C.toSimplicialCat n) ≫
    DaggerNerve.daggerCoherentNerve.map (degreeToDaggerCotensor C n.unop)

/-- All original parameter operators commute with the SAME full comparison. -/
def comparison (C : DaggerSimplicialCat.{u, u}) :
    degreeDiagram C ⟶ DaggerNativeDaggerCotensorResolution.resolution C where
  app := comparisonApp C
  naturality _ _ a := by
    apply DaggerSSet.Hom.ext
    exact (DaggerNativeDegreeCotensorComparison.comparison C.toSimplicialCat).naturality a

/-- The ENTIRE old bisimplicial comparison component remains unchanged. -/
theorem comparison_hom (C : DaggerSimplicialCat.{u, u}) (n : SimplexCategoryᵒᵖ) :
    ((comparison C).app n).hom =
      (DaggerNativeDegreeCotensorComparison.comparison C.toSimplicialCat).app n := rfl

end
end DaggerNativeDaggerDegreeNerveComparison
