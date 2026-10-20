import ActualKanSimplexCotensorComparison
import ActualQKanCotensorComparison

/-! The original singular complex maps weakly to the diagonal of standard-simplex cotensors. -/

set_option autoImplicit false
open CategoryTheory MonoidalCategory MonoidalClosed Opposite Simplicial
open DaggerOriginalFixedObjectCotensorPoints DaggerSSetGluing
open DaggerOriginalCounitRightConeQRealizationAdjunction
open DaggerActualKanCotensorParameterWeakEquivalences
open scoped SSet.modelCategoryQuillen
universe u

namespace DaggerActualQSingularSimplexCotensorDiagonal
noncomputable section

/-- Native standard-simplex cotensors retain every simplex-category operator. -/
def simplexCotensors (X : SSet.{u}) : SimplicialObject SSet.{u} :=
  SSet.stdSimplex.{u}.op ⋙ parameterFunctor X

/-- Apply the literal original-Q singular functor in every standard-simplex degree. -/
def singularMixed (X : SSet.{u}) : SimplicialObject SSet.{u} :=
  simplexCotensors X ⋙ singular.{u}

/-- The singular image of every original standard-simplex constant is natural. -/
def constants (X : SSet.{u}) :
    (Functor.const SimplexCategoryᵒᵖ).obj (singular.obj X) ⟶ singularMixed X where
  app n := singular.map (constantHom (SSet.stdSimplex.obj n.unop) X)
  naturality n m i := by
    change 𝟙 (singular.obj X) ≫ singular.map (constantHom (SSet.stdSimplex.obj m.unop) X) =
      singular.map (constantHom (SSet.stdSimplex.obj n.unop) X) ≫
        singular.map ((MonoidalClosed.pre (SSet.stdSimplex.map i.unop)).app X)
    rw [Category.id_comp, ← singular.map_comp, constantHom_parameter]

/-- Each entire singular row is weak by the previously proved native Brown theorem. -/
theorem constants_row_GW (X : SSet.{u}) [X.KanComplex] (n : SimplexCategoryᵒᵖ) :
    GW ((constants X).app n) :=
  DaggerActualKanSimplexCotensorComparison.singular_simplex_constants_GW X n.unop.len

/-- The diagonal of an outer constant simplicial set is literally its original simplicial set. -/
def diagonalComparison (X : SSet.{u}) :
    singular.obj X ⟶ DaggerBisimplicialDiagonal.diag (singularMixed X) :=
  DaggerBisimplicialDiagonal.diagMap (constants X)

/-- This is an actual weak map from the unchanged original-Q singular complex. -/
theorem diagonalComparison_GW (X : SSet.{u}) [X.KanComplex] :
    GW (diagonalComparison X) :=
  DaggerOriginalDiagonalGeometric.diagMap_geometric_row (constants X) (constants_row_GW X)

end
end DaggerActualQSingularSimplexCotensorDiagonal
