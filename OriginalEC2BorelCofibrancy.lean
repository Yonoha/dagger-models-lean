import OriginalEC2EquivariantRelativeCellComplex
import TopCatModelCategory.ModelCategoryTopCat
import Mathlib.CategoryTheory.SmallObject.TransfiniteCompositionLifting

/-!
# Lifting criterion for the realized original EC₂ cell complex

The right class consists of equivariant maps whose underlying maps have the
right lifting property against all realized simplex boundary inclusions.
The resulting left class is a lifting-property class in `Action TopCat C2`;
this file does not postulate a model structure on that action category.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Opposite Simplicial
open DaggerOriginalDaggerRealizationC2Action DaggerOriginalEC2SimplicialAction
open DaggerOriginalEC2SkeletonAction DaggerOriginalEC2EquivariantSkeletalPushout
open DaggerOriginalEC2EquivariantRelativeCellComplex

universe u

namespace DaggerOriginalEC2BorelCofibrancy

noncomputable section

/-- Equivariant maps whose underlying topological maps are trivial fibrations,
expressed by the boundary-inclusion lifting characterization. -/
def borelTrivialFibrations : MorphismProperty (Action TopCat.{u} C2.{u}) :=
  TopCat.modelCategory.I.rlp.inverseImage (Action.forget TopCat.{u} C2.{u})

/-- The corresponding projective/Borel left lifting class. -/
def borelCofibrations : MorphismProperty (Action TopCat.{u} C2.{u}) :=
  borelTrivialFibrations.{u}.llp

/-- The exhaustive realized cell filtration reduces the full inclusion's
lifting property to the genuine free-orbit boundary cells. -/
theorem realizedSkeletalInclusion_borel_of_cells
    (hcell : ∀ n : ℕ, borelCofibrations.{u}
      ((SSet.toTop.{u}.mapAction C2.{u}).map (boundaryHom.{u} n))) :
    borelCofibrations.{u}
      ((SSet.toTop.{u}.mapAction C2.{u}).map (skeletonInclusion.{u} 0)) := by
  let c : RelativeCellComplex.{0}
      (fun (n : ℕ) (_ : PUnit.{1}) ↦
        (SSet.toTop.{u}.mapAction C2.{u}).map (boundaryHom.{u} n))
      ((SSet.toTop.{u}.mapAction C2.{u}).map (skeletonInclusion.{u} 0)) :=
    realizedEquivariantRelativeCellComplex.{u}
  have : borelCofibrations.{u}.IsStableUnderTransfiniteCompositionOfShape ℕ := by
    unfold borelCofibrations
    infer_instance
  have : borelCofibrations.{u}.IsStableUnderCobaseChange := by
    unfold borelCofibrations
    infer_instance
  apply borelCofibrations.{u}.transfiniteCompositionsOfShape_le ℕ
  refine ⟨{
    toTransfiniteCompositionOfShape := c.toTransfiniteCompositionOfShape
    map_mem := ?_
  }⟩
  intro n hn
  exact borelCofibrations.{u}.of_isPushout
    (realizedEquivariantSkeletalPushout.{u} n) (hcell n)

end

end DaggerOriginalEC2BorelCofibrancy
