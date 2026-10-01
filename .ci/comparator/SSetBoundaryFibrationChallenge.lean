import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations

/-! Ordinary SSet input toward Part I `bg.lem.I-inj`.
Actual boundary lifting implies the existing Mathlib Kan fibration predicate.
This does not assert a weak homotopy equivalence or a model structure. -/
set_option warningAsError false
universe u

namespace DaggerModels.SSetBoundaryFibration

open SSet.modelCategoryQuillen in
theorem boundary_rlp_le_fibrations : SSet.modelCategoryQuillen.I.{u}.rlp ≤
    HomotopicalAlgebra.fibrations SSet.{u} := by sorry

end DaggerModels.SSetBoundaryFibration
