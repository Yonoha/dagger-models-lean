import AmalgamEvaluation
import AmalgamPaddedStages

/-! The four original simplicial evaluations land in their actual rank stages.
Their complete unit-boundary is exactly the inverse image of the preceding stage. -/

open CategoryTheory DaggerModels DaggerAmalgamPresentation
open DaggerAmalgamUnitBoundary DaggerAmalgamPaddedClassifier
open DaggerAmalgamRankFiltration

universe u

set_option autoImplicit false

namespace DaggerAmalgamSuccessor

noncomputable section

variable (C B : SimplicialCat.{u, u}) (x : C.Obj) (b : B.Obj)

theorem boundaryOO_iff_critical (a d : C.Obj) (n : ℕ) (q : SimplexCategoryᵒᵖ)
    (v : (familyOO C B x b a d n).obj q) :
    v ∈ (boundaryOO C B x b a d n).obj q ↔
      criticalOO C B x b q a d n (familyOO_degreeEquiv C B x b a d n q v) := by
  cases n with
  | zero => simp [boundaryOO, criticalOO]
  | succ n => exact mem_boundaryOO_succ C B x b a d n q v

theorem boundaryON_iff_critical (a : C.Obj) (w : B.Obj) (n : ℕ)
    (q : SimplexCategoryᵒᵖ) (v : (familyON C B x b a w n).obj q) :
    v ∈ (boundaryON C B x b a w n).obj q ↔
      criticalON C B x b q a w n (familyON_degreeEquiv C B x b a w n q v) :=
  mem_boundaryON C B x b a w n q v

theorem boundaryNO_iff_critical (z : B.Obj) (d : C.Obj) (n : ℕ)
    (q : SimplexCategoryᵒᵖ) (v : (familyNO C B x b z d n).obj q) :
    v ∈ (boundaryNO C B x b z d n).obj q ↔
      criticalNO C B x b q z d n (familyNO_degreeEquiv C B x b z d n q v) :=
  mem_boundaryNO C B x b z d n q v

theorem boundaryNN_iff_critical (z w : B.Obj) (n : ℕ) (q : SimplexCategoryᵒᵖ)
    (v : (familyNN C B x b z w n).obj q) :
    v ∈ (boundaryNN C B x b z w n).obj q ↔
      criticalNN C B x b q z w n (familyNN_degreeEquiv C B x b z w n q v) := by
  cases n with
  | zero => simp [boundaryNN, criticalNN]
  | succ n => exact mem_boundaryNN_succ C B x b z w n q v

theorem evaluationOO_range (a d : C.Obj) (n : ℕ) :
    SSet.Subcomplex.range (evaluationOO C B x b a d n) ≤ oldOldStage C B x b n a d := by
  intro q h hh
  obtain ⟨v, rfl⟩ := hh
  exact evalOO_mem_stage C B x b q a d n (familyOO_degreeEquiv C B x b a d n q v)

theorem evaluationON_range (a : C.Obj) (w : B.Obj) (n : ℕ) :
    SSet.Subcomplex.range (evaluationON C B x b a w n) ≤ oldNewStage C B x b n a w := by
  intro q h hh
  obtain ⟨v, rfl⟩ := hh
  exact evalON_mem_stage C B x b q a w n (familyON_degreeEquiv C B x b a w n q v)

theorem evaluationNO_range (z : B.Obj) (d : C.Obj) (n : ℕ) :
    SSet.Subcomplex.range (evaluationNO C B x b z d n) ≤ newOldStage C B x b n z d := by
  intro q h hh
  obtain ⟨v, rfl⟩ := hh
  exact evalNO_mem_stage C B x b q z d n (familyNO_degreeEquiv C B x b z d n q v)

theorem evaluationNN_range (z w : B.Obj) (n : ℕ) :
    SSet.Subcomplex.range (evaluationNN C B x b z w n) ≤ newNewStage C B x b n z w := by
  intro q h hh
  obtain ⟨v, rfl⟩ := hh
  exact evalNN_mem_stage C B x b q z w n (familyNN_degreeEquiv C B x b z w n q v)

def evaluationStageOO (a d : C.Obj) (n : ℕ) :
    familyOO C B x b a d n ⟶ (oldOldStage C B x b n a d : SSet.{u}) :=
  SSet.Subcomplex.lift _ (evaluationOO_range C B x b a d n)

def evaluationStageON (a : C.Obj) (w : B.Obj) (n : ℕ) :
    familyON C B x b a w n ⟶ (oldNewStage C B x b n a w : SSet.{u}) :=
  SSet.Subcomplex.lift _ (evaluationON_range C B x b a w n)

def evaluationStageNO (z : B.Obj) (d : C.Obj) (n : ℕ) :
    familyNO C B x b z d n ⟶ (newOldStage C B x b n z d : SSet.{u}) :=
  SSet.Subcomplex.lift _ (evaluationNO_range C B x b z d n)

def evaluationStageNN (z w : B.Obj) (n : ℕ) :
    familyNN C B x b z w n ⟶ (newNewStage C B x b n z w : SSet.{u}) :=
  SSet.Subcomplex.lift _ (evaluationNN_range C B x b z w n)

theorem evaluationOO_mem_previous_iff (a d : C.Obj) (n : ℕ)
    (q : SimplexCategoryᵒᵖ) (v : (familyOO C B x b a d (n + 1)).obj q) :
    (evaluationOO C B x b a d (n + 1)).app q v ∈ (oldOldStage C B x b n a d).obj q ↔
      v ∈ (boundaryOO C B x b a d (n + 1)).obj q :=
  (evalOO_mem_previous_iff C B x b q a d n
    (familyOO_degreeEquiv C B x b a d (n + 1) q v)).trans
      (boundaryOO_iff_critical C B x b a d (n + 1) q v).symm

theorem evaluationON_mem_previous_iff (a : C.Obj) (w : B.Obj) (hw : w ≠ b) (n : ℕ)
    (q : SimplexCategoryᵒᵖ) (v : (familyON C B x b a w (n + 1)).obj q) :
    (evaluationON C B x b a w (n + 1)).app q v ∈ (oldNewStage C B x b n a w).obj q ↔
      v ∈ (boundaryON C B x b a w (n + 1)).obj q :=
  (evalON_mem_previous_iff C B x b q a w hw n
    (familyON_degreeEquiv C B x b a w (n + 1) q v)).trans
      (boundaryON_iff_critical C B x b a w (n + 1) q v).symm

theorem evaluationNO_mem_previous_iff (z : B.Obj) (d : C.Obj) (hz : z ≠ b) (n : ℕ)
    (q : SimplexCategoryᵒᵖ) (v : (familyNO C B x b z d (n + 1)).obj q) :
    (evaluationNO C B x b z d (n + 1)).app q v ∈ (newOldStage C B x b n z d).obj q ↔
      v ∈ (boundaryNO C B x b z d (n + 1)).obj q :=
  (evalNO_mem_previous_iff C B x b q z d hz n
    (familyNO_degreeEquiv C B x b z d (n + 1) q v)).trans
      (boundaryNO_iff_critical C B x b z d (n + 1) q v).symm

theorem evaluationNN_mem_previous_iff (z w : B.Obj) (hz : z ≠ b) (hw : w ≠ b) (n : ℕ)
    (q : SimplexCategoryᵒᵖ) (v : (familyNN C B x b z w (n + 1)).obj q) :
    (evaluationNN C B x b z w (n + 1)).app q v ∈ (newNewStage C B x b n z w).obj q ↔
      v ∈ (boundaryNN C B x b z w (n + 1)).obj q :=
  (evalNN_mem_previous_iff C B x b q z w hz hw n
    (familyNN_degreeEquiv C B x b z w (n + 1) q v)).trans
      (boundaryNN_iff_critical C B x b z w (n + 1) q v).symm

end
end DaggerAmalgamSuccessor
