import AmalgamZeroStage
import AmalgamFirstStageComparison
import AmalgamPaddedSmallFaces

/-! The exceptional first NN square uses the original B composition and original C unit. -/

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open DaggerModels DaggerAmalgamPresentation DaggerAmalgamUnitBoundary
open DaggerAmalgamPaddedClassifier DaggerAmalgamLowRankProducts
open DaggerAmalgamRankFiltration

universe u

set_option autoImplicit false

namespace DaggerAmalgamSuccessor

noncomputable section

variable (C B : SimplicialCat.{u, u}) (x : C.Obj) (b : B.Obj)

/-- Remove the specified sole C-loop unit and compose the two original B endpoint arrows. -/
theorem boundaryNN_one_eval (z w : B.Obj) (q : SimplexCategoryᵒᵖ)
    (v : (boundaryNN C B x b z w 1 : SSet.{u}).obj q) :
    evalNN C B x b q z w 1 v.val =
      evalNN C B x b q z w 0 ((eComp SSet z b w).app q (v.val.1, v.val.2.2.2)) := by
  let fd := faceNN_C C B x b q z w 0 v.val 0
    ((mem_boundaryNN_one C B x b z w q v.val).1 v.property)
  have he := rawFaceNN_eval C B x b q z w 0 v.val _ fd
  rw [rawFaceNN_one_composition C B x b q z w v.val fd] at he
  exact he.symm

theorem boundaryNN_one_original_comp (z w : B.Obj) (hz : z ≠ b) (hw : w ≠ b) :
    (oneNNBoundaryIso C B x b z w).inv ≫ boundaryStageNN C B x b z w hz hw 0 =
      (eComp SSet z b w) ≫ (zeroStageNNIso C B x b z w hz hw).hom := by
  ext q v
  exact boundaryNN_one_eval C B x b z w q ((oneNNBoundaryIso C B x b z w).inv.app q v)

/-- Original B Hom embeds in the SAME first rank stage. -/
def firstStageOldNN (z w : B.Obj) (hz : z ≠ b) (hw : w ≠ b) :
    (z ⟶[SSet] w) ⟶ (newNewStage C B x b 1 z w : SSet.{u}) :=
  (zeroStageNNIso C B x b z w hz hw).hom ≫ successorNN C B x b z w 0

/-- The complete original middle-coordinate product evaluates into the SAME first rank stage. -/
def firstStageProductNN (z w : B.Obj) :
    ((z ⟶[SSet] b) ⊗ (x ⟶[SSet] x)) ⊗ (b ⟶[SSet] w) ⟶
      (newNewStage C B x b 1 z w : SSet.{u}) :=
  (oneNNIso C B x b z w).inv ≫ evaluationStageNN C B x b z w 1

theorem firstStageNN_isPushout (z w : B.Obj) (hz : z ≠ b) (hw : w ≠ b) :
    IsPushout (eComp SSet z b w)
      (DaggerAmalgamFirstStage.atRight (z ⟶[SSet] b) (eId SSet x) ▷ (b ⟶[SSet] w))
      (firstStageOldNN C B x b z w hz hw) (firstStageProductNN C B x b z w) := by
  apply (successorNN_isPushout C B x b z w hz hw 0).of_iso'
    (oneNNBoundaryIso C B x b z w).symm (zeroStageNNIso C B x b z w hz hw)
    (oneNNIso C B x b z w).symm (Iso.refl _)
  · exact boundaryNN_one_original_comp C B x b z w hz hw
  · apply (cancel_mono (oneNNIso C B x b z w).hom).1
    simp only [Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [← oneNNBoundaryIso_square]
    simp
  · simp only [Iso.refl_hom, Category.comp_id]
    rfl
  · simp only [Iso.symm_hom, Iso.refl_hom, Category.comp_id]
    rfl

end
end DaggerAmalgamSuccessor
