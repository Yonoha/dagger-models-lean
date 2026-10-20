import ActualKanCotensorParameterWeakEquivalences
import ActualCounitRightConeHomContractibility
import OriginalDiagonalGeometricReconciledRecovered

/-! Constants compare the original Kan complex to the diagonal of its original-Q cotensors. -/

set_option autoImplicit false
open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonoidalClosed
open Opposite Simplicial HomotopicalAlgebra
open DaggerOriginalCounitRightCone DaggerOriginalCounitRightConeQFunctor
open DaggerOriginalFixedObjectCotensorPoints DaggerSSetGluing
open DaggerActualKanCotensorParameterWeakEquivalences
open scoped SSet.modelCategoryQuillen
universe u

namespace DaggerActualQKanCotensorComparison
noncomputable section

/-- The literal Q cotensors, with all original cosimplicial operators retained. -/
def mixed (X : SSet.{u}) : SimplicialObject SSet.{u} :=
  QFunctor.{u}.op ⋙ parameterFunctor X

/-- Native constants are natural in every original Q parameter. -/
def constants (X : SSet.{u}) :
    (Functor.const SimplexCategoryᵒᵖ).obj X ⟶ mixed X where
  app n := constantHom (QFunctor.obj n.unop) X
  naturality n m i := by
    change 𝟙 X ≫ constantHom (QFunctor.obj m.unop) X =
      constantHom (QFunctor.obj n.unop) X ≫ (MonoidalClosed.pre (QFunctor.map i.unop)).app X
    rw [Category.id_comp]
    exact (constantHom_parameter (QFunctor.map i.unop) X).symm

/-- The actual original-Q contractibility proves weakness of every full row. -/
theorem constants_row_GW (X : SSet.{u}) [X.KanComplex] (n : SimplexCategoryᵒᵖ) :
    GW ((constants X).app n) := by
  exact constantHom_GW (Q n.unop.len) X
    (DaggerActualCounitRightConeHomContractibility.Q_toUnit_GW n.unop.len)

/-- Reuse the existing unrestricted bisimplicial row theorem, without a Reedy premise. -/
theorem diagonal_constants_GW (X : SSet.{u}) [X.KanComplex] :
    GW (DaggerBisimplicialDiagonal.diagMap (constants X)) :=
  DaggerOriginalDiagonalGeometric.diagMap_geometric_row (constants X) (constants_row_GW X)

end
end DaggerActualQKanCotensorComparison
