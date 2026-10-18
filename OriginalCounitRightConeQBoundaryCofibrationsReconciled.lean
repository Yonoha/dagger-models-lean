import OriginalCounitRightConeQAllBoundaryMonoReconciled
import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations

/-!
# Cofibrations of the literal right-cone Q boundary comparisons

The actual boundary-indexed comparisons are monomorphisms in all degrees.
The existing simplicial-set cofibration structure identifies monomorphisms
with cofibrations, so no new model-category structure is postulated here.
-/

set_option autoImplicit false

open CategoryTheory HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen
open DaggerOriginalCounitRightConeQLatching
open DaggerOriginalCounitRightConeQAllBoundaryMono

universe u

namespace DaggerOriginalCounitRightConeQBoundaryCofibrations

noncomputable section

/-- The original boundary Q comparison is a simplicial-set cofibration in every degree. -/
theorem boundaryQMap_cofibration (n : ℕ) : Cofibration (boundaryQMap.{u} n) := by
  haveI := boundaryQMap_mono.{u} n
  exact SSet.modelCategoryQuillen.cofibration_of_mono _

end

end DaggerOriginalCounitRightConeQBoundaryCofibrations
