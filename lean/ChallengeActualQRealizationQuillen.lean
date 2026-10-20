import OriginalCounitRightConeQRealizationAdjunctionReconciled
import Mathlib.AlgebraicTopology.SimplicialSet.Horn
import TopCatModelCategory.QuillenAdjunction

/-! Quillen property and every actual horn for the literal original-Q adjunction. -/

set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra Simplicial
open DaggerOriginalCounitRightConeQRealizationAdjunction
open scoped SSet.modelCategoryQuillen
universe u

namespace DaggerActualQRealizationQuillenChallenge

def statement : Prop :=
  realizationSingularAdjunction.{u}.IsQuillenAdjunction ∧
    ∀ n : ℕ, ∀ i : Fin (n + 2),
      trivialCofibrations SSet.{u} (realization.{u}.map (SSet.horn.{u} (n + 1) i).ι)

end DaggerActualQRealizationQuillenChallenge
