import NativeGeometricTotalPiFunctor
import NativeBasedPiFreeEvaluationPullback

/-! Geometric based-pi rows are the actual pullback along original realization-unit vertices. -/
set_option autoImplicit false
open CategoryTheory Limits Simplicial HomotopicalAlgebra
open DaggerNativeGeometricTotalPiFunctor DaggerNativeBasedPiFreeEvaluationPullback
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeGeometricPiVertexPullback
noncomputable section

def geometricRows (F : SimplexCategoryᵒᵖ ⥤ SSet.{u}) (n : ℕ) : SSet.{u} :=
  F ⋙ geometricPiFunctor n

def geometricProjection (F : SimplexCategoryᵒᵖ ⥤ SSet.{u}) (n : ℕ) :
    geometricRows F n ⟶ vertexRows F := Functor.whiskerLeft F (geometricVertexProjection n)

def unitVertexRows (F : SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    vertexRows F ⟶ vertexRows (F ⋙ singularRealization) := Functor.whiskerLeft F unitVertices

def toSingularRows (F : SimplexCategoryᵒᵖ ⥤ SSet.{u}) (n : ℕ) :
    geometricRows F n ⟶ basedRows (F ⋙ singularRealization) n :=
  Functor.whiskerLeft F (toSingularTotalPi n)

theorem toSingularRows_projection (F : SimplexCategoryᵒᵖ ⥤ SSet.{u}) (n : ℕ) :
    toSingularRows F n ≫ basedProjection (F ⋙ singularRealization) n =
      geometricProjection F n ≫ unitVertexRows F := by
  apply NatTrans.ext
  rfl

def comparisonMap (F : SimplexCategoryᵒᵖ ⥤ SSet.{u}) (n : ℕ) : geometricRows F n ⟶
    pullback (basedProjection (F ⋙ singularRealization) n) (unitVertexRows F) :=
  pullback.lift (toSingularRows F n) (geometricProjection F n)
    (toSingularRows_projection F n)

theorem comparisonMap_fst (F : SimplexCategoryᵒᵖ ⥤ SSet.{u}) (n : ℕ) :
    comparisonMap F n ≫ pullback.fst
      (basedProjection (F ⋙ singularRealization) n) (unitVertexRows F) =
        toSingularRows F n := by
  simp only [comparisonMap, pullback.lift_fst]

theorem comparisonMap_snd (F : SimplexCategoryᵒᵖ ⥤ SSet.{u}) (n : ℕ) :
    comparisonMap F n ≫ pullback.snd
      (basedProjection (F ⋙ singularRealization) n) (unitVertexRows F) =
        geometricProjection F n := by
  simp only [comparisonMap, pullback.lift_snd]

end
end DaggerNativeGeometricPiVertexPullback
