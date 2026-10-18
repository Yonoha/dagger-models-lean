import AmalgamStageCoverage
import AmalgamAttachmentCriterion

/-! All four actual successor squares satisfy the full simplicial pushout property.
The arrows are the original boundary inclusion and original rank-stage evaluations. -/

open CategoryTheory Limits DaggerModels DaggerAmalgamPresentation
open DaggerAmalgamUnitBoundary DaggerAmalgamRankFiltration

universe u

set_option autoImplicit false

namespace DaggerAmalgamSuccessor

noncomputable section

variable (C B : SimplicialCat.{u, u}) (x : C.Obj) (b : B.Obj)

def successorOO (a d : C.Obj) (n : ℕ) :
    (oldOldStage C B x b n a d : SSet.{u}) ⟶
      (oldOldStage C B x b (n + 1) a d : SSet.{u}) :=
  SSet.Subcomplex.homOfLE (stage_monotone C B x b false _ _ (Nat.le_succ n))

def boundaryStageOO (a d : C.Obj) (n : ℕ) :
    (boundaryOO C B x b a d (n + 1) : SSet.{u}) ⟶
      (oldOldStage C B x b n a d : SSet.{u}) :=
  DaggerAmalgamAttachment.boundaryToStage (oldOldStage C B x b n a d)
    (boundaryOO C B x b a d (n + 1)) (evaluationOO C B x b a d (n + 1))
    (evaluationOO_mem_previous_iff C B x b a d n)

/-- Full unrestricted pushout, with the original four arrows. -/
theorem successorOO_isPushout (a d : C.Obj) (n : ℕ) :
    IsPushout (boundaryStageOO C B x b a d n)
      (boundaryOO C B x b a d (n + 1)).ι (successorOO C B x b a d n)
      (evaluationStageOO C B x b a d (n + 1)) :=
  DaggerAmalgamAttachment.isPushout (oldOldStage C B x b n a d)
    (oldOldStage C B x b (n + 1) a d)
    (stage_monotone C B x b false _ _ (Nat.le_succ n))
    (boundaryOO C B x b a d (n + 1)) (evaluationOO C B x b a d (n + 1))
    (evaluationOO_range C B x b a d (n + 1))
    (evaluationOO_mem_previous_iff C B x b a d n)
    (evaluationOO_covers_successor C B x b a d n)
    (evaluationOO_interior_injective C B x b a d (n + 1))

def successorON (a : C.Obj) (w : B.Obj) (n : ℕ) :
    (oldNewStage C B x b n a w : SSet.{u}) ⟶
      (oldNewStage C B x b (n + 1) a w : SSet.{u}) :=
  SSet.Subcomplex.homOfLE (stage_monotone C B x b true _ _ (Nat.le_succ n))

def boundaryStageON (a : C.Obj) (w : B.Obj) (hw : w ≠ b) (n : ℕ) :
    (boundaryON C B x b a w (n + 1) : SSet.{u}) ⟶
      (oldNewStage C B x b n a w : SSet.{u}) :=
  DaggerAmalgamAttachment.boundaryToStage (oldNewStage C B x b n a w)
    (boundaryON C B x b a w (n + 1)) (evaluationON C B x b a w (n + 1))
    (evaluationON_mem_previous_iff C B x b a w hw n)

/-- Full unrestricted pushout, with the original four arrows. -/
theorem successorON_isPushout (a : C.Obj) (w : B.Obj) (hw : w ≠ b) (n : ℕ) :
    IsPushout (boundaryStageON C B x b a w hw n)
      (boundaryON C B x b a w (n + 1)).ι (successorON C B x b a w n)
      (evaluationStageON C B x b a w (n + 1)) :=
  DaggerAmalgamAttachment.isPushout (oldNewStage C B x b n a w)
    (oldNewStage C B x b (n + 1) a w)
    (stage_monotone C B x b true _ _ (Nat.le_succ n))
    (boundaryON C B x b a w (n + 1)) (evaluationON C B x b a w (n + 1))
    (evaluationON_range C B x b a w (n + 1))
    (evaluationON_mem_previous_iff C B x b a w hw n)
    (evaluationON_covers_successor C B x b a w hw n)
    (evaluationON_interior_injective C B x b a w hw (n + 1))

def successorNO (z : B.Obj) (d : C.Obj) (n : ℕ) :
    (newOldStage C B x b n z d : SSet.{u}) ⟶
      (newOldStage C B x b (n + 1) z d : SSet.{u}) :=
  SSet.Subcomplex.homOfLE (stage_monotone C B x b true _ _ (Nat.le_succ n))

def boundaryStageNO (z : B.Obj) (d : C.Obj) (hz : z ≠ b) (n : ℕ) :
    (boundaryNO C B x b z d (n + 1) : SSet.{u}) ⟶
      (newOldStage C B x b n z d : SSet.{u}) :=
  DaggerAmalgamAttachment.boundaryToStage (newOldStage C B x b n z d)
    (boundaryNO C B x b z d (n + 1)) (evaluationNO C B x b z d (n + 1))
    (evaluationNO_mem_previous_iff C B x b z d hz n)

/-- Full unrestricted pushout, with the original four arrows. -/
theorem successorNO_isPushout (z : B.Obj) (d : C.Obj) (hz : z ≠ b) (n : ℕ) :
    IsPushout (boundaryStageNO C B x b z d hz n)
      (boundaryNO C B x b z d (n + 1)).ι (successorNO C B x b z d n)
      (evaluationStageNO C B x b z d (n + 1)) :=
  DaggerAmalgamAttachment.isPushout (newOldStage C B x b n z d)
    (newOldStage C B x b (n + 1) z d)
    (stage_monotone C B x b true _ _ (Nat.le_succ n))
    (boundaryNO C B x b z d (n + 1)) (evaluationNO C B x b z d (n + 1))
    (evaluationNO_range C B x b z d (n + 1))
    (evaluationNO_mem_previous_iff C B x b z d hz n)
    (evaluationNO_covers_successor C B x b z d hz n)
    (evaluationNO_interior_injective C B x b z d hz (n + 1))

def successorNN (z w : B.Obj) (n : ℕ) :
    (newNewStage C B x b n z w : SSet.{u}) ⟶
      (newNewStage C B x b (n + 1) z w : SSet.{u}) :=
  SSet.Subcomplex.homOfLE (stage_monotone C B x b true _ _ (Nat.le_succ n))

def boundaryStageNN (z w : B.Obj) (hz : z ≠ b) (hw : w ≠ b) (n : ℕ) :
    (boundaryNN C B x b z w (n + 1) : SSet.{u}) ⟶
      (newNewStage C B x b n z w : SSet.{u}) :=
  DaggerAmalgamAttachment.boundaryToStage (newNewStage C B x b n z w)
    (boundaryNN C B x b z w (n + 1)) (evaluationNN C B x b z w (n + 1))
    (evaluationNN_mem_previous_iff C B x b z w hz hw n)

/-- Full unrestricted pushout, with the original four arrows. -/
theorem successorNN_isPushout (z w : B.Obj) (hz : z ≠ b) (hw : w ≠ b) (n : ℕ) :
    IsPushout (boundaryStageNN C B x b z w hz hw n)
      (boundaryNN C B x b z w (n + 1)).ι (successorNN C B x b z w n)
      (evaluationStageNN C B x b z w (n + 1)) :=
  DaggerAmalgamAttachment.isPushout (newNewStage C B x b n z w)
    (newNewStage C B x b (n + 1) z w)
    (stage_monotone C B x b true _ _ (Nat.le_succ n))
    (boundaryNN C B x b z w (n + 1)) (evaluationNN C B x b z w (n + 1))
    (evaluationNN_range C B x b z w (n + 1))
    (evaluationNN_mem_previous_iff C B x b z w hz hw n)
    (evaluationNN_covers_successor C B x b z w hz hw n)
    (evaluationNN_interior_injective C B x b z w hz hw (n + 1))

theorem evaluationStageOO_ι (a d : C.Obj) (n : ℕ) :
    evaluationStageOO C B x b a d n ≫ (oldOldStage C B x b n a d).ι =
      evaluationOO C B x b a d n := by
  ext q v
  rfl

theorem boundaryStageOO_ι (a d : C.Obj) (n : ℕ) :
    boundaryStageOO C B x b a d n ≫ (oldOldStage C B x b n a d).ι =
      (boundaryOO C B x b a d (n + 1)).ι ≫ evaluationOO C B x b a d (n + 1) := by
  ext q v
  rfl

theorem evaluationStageON_ι (a : C.Obj) (w : B.Obj) (n : ℕ) :
    evaluationStageON C B x b a w n ≫ (oldNewStage C B x b n a w).ι =
      evaluationON C B x b a w n := by
  ext q v
  rfl

theorem boundaryStageON_ι (a : C.Obj) (w : B.Obj) (hw : w ≠ b) (n : ℕ) :
    boundaryStageON C B x b a w hw n ≫ (oldNewStage C B x b n a w).ι =
      (boundaryON C B x b a w (n + 1)).ι ≫ evaluationON C B x b a w (n + 1) := by
  ext q v
  rfl

theorem evaluationStageNO_ι (z : B.Obj) (d : C.Obj) (n : ℕ) :
    evaluationStageNO C B x b z d n ≫ (newOldStage C B x b n z d).ι =
      evaluationNO C B x b z d n := by
  ext q v
  rfl

theorem boundaryStageNO_ι (z : B.Obj) (d : C.Obj) (hz : z ≠ b) (n : ℕ) :
    boundaryStageNO C B x b z d hz n ≫ (newOldStage C B x b n z d).ι =
      (boundaryNO C B x b z d (n + 1)).ι ≫ evaluationNO C B x b z d (n + 1) := by
  ext q v
  rfl

theorem evaluationStageNN_ι (z w : B.Obj) (n : ℕ) :
    evaluationStageNN C B x b z w n ≫ (newNewStage C B x b n z w).ι =
      evaluationNN C B x b z w n := by
  ext q v
  rfl

theorem boundaryStageNN_ι (z w : B.Obj) (hz : z ≠ b) (hw : w ≠ b) (n : ℕ) :
    boundaryStageNN C B x b z w hz hw n ≫ (newNewStage C B x b n z w).ι =
      (boundaryNN C B x b z w (n + 1)).ι ≫ evaluationNN C B x b z w (n + 1) := by
  ext q v
  rfl

end
end DaggerAmalgamSuccessor
