import OriginalSimplicialActionModelCategory
import OriginalEC2EquivariantRelativeCellComplex
import Mathlib.CategoryTheory.SmallObject.TransfiniteCompositionLifting

/-!
# Projective cofibrancy of the literal original simplicial EC₂

The existing original regular cell action and cell map are definitionally Mathlib's native
free action and map. The already verified original equivariant skeletal attaching pushouts
and exhaustive relative cell complex therefore consist of projective cofibrations in the
actual simplicial action model. Transport from its original zero skeleton to the canonical
initial arrow proves cofibrancy of the same codiscrete nerve with the same regular action.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra MorphismProperty
open DaggerOriginalDaggerRealizationC2Action DaggerOriginalEC2SimplicialAction
open DaggerOriginalEC2FreeCellAction DaggerOriginalEC2SkeletonAction
open DaggerOriginalEC2EquivariantSkeletalPushout DaggerOriginalEC2EquivariantRelativeCellComplex
open DaggerOriginalSimplicialActionFreeGenerators DaggerOriginalSimplicialActionModelCategory
open scoped SSet.modelCategoryQuillen DaggerOriginalSimplicialActionModelCategory

universe u

namespace DaggerOriginalEC2SimplicialProjectiveCofibrancy

noncomputable section

/-- The existing original regular free simplicial action is exactly the native free action. -/
theorem freeCellAction_eq_native (A : SSet.{u}) : freeCellAction A = free.obj A := rfl

/-- The existing original componentwise regular cell map is exactly the native free map. -/
theorem freeCellMap_eq_native {A B : SSet.{u}} (i : A ⟶ B) : freeCellMap i = free.map i := rfl

/-- Every original regular boundary-cell orbit is a projective cofibration. -/
theorem originalBoundary_projectiveCofibration (n : ℕ) : Cofibration (boundaryHom.{u} n) := by
  rw [cofibration_iff_original]
  change I.rlp.llp (free.map (SSet.boundary.{u} n).ι)
  exact (le_llp_rlp I) _ (ofHoms.mk n)

/-- The original exhaustive skeletal inclusion is a projective cofibration. -/
theorem originalSkeletalInclusion_projectiveCofibration :
    Cofibration (skeletonInclusion.{u} 0) := by
  let c : RelativeCellComplex.{0}
      (fun (n : ℕ) (_ : PUnit.{1}) ↦ boundaryHom.{u} n) (skeletonInclusion.{u} 0) :=
    equivariantRelativeCellComplex.{u}
  rw [cofibration_iff]
  apply (cofibrations (Action SSet.{u} C2.{u})).transfiniteCompositionsOfShape_le ℕ
  refine ⟨{
    toTransfiniteCompositionOfShape := c.toTransfiniteCompositionOfShape
    map_mem := ?_
  }⟩
  intro n hn
  exact (cofibrations (Action SSet.{u} C2.{u})).of_isPushout
    (equivariantSkeletalPushout.{u} n)
    ((cofibration_iff (boundaryHom.{u} n)).1 (originalBoundary_projectiveCofibration n))

/-- The original simplicial EC₂ action is cofibrant in the actual projective model. -/
instance originalSimplicialEC2_isCofibrant : IsCofibrant simplicialAction.{u} := by
  let e := initialIsoIsInitial (skeletalZeroIsInitial.{u})
  have h : (initial.to simplicialAction.{u}) = e.hom ≫ skeletonInclusion.{u} 0 :=
    initialIsInitial.hom_ext _ _
  rw [isCofibrant_iff, h]
  have : Cofibration (skeletonInclusion.{u} 0) := originalSkeletalInclusion_projectiveCofibration
  infer_instance

end

end DaggerOriginalEC2SimplicialProjectiveCofibrancy
