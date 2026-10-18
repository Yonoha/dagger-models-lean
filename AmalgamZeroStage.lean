import AmalgamSuccessorPushouts
import AmalgamPaddedBases
import Mathlib.CategoryTheory.NatIso
import Mathlib.CategoryTheory.Types.Basic

/-! Each original rank-zero evaluation is an isomorphism of whole simplicial sets. -/

open CategoryTheory DaggerModels DaggerAmalgamPresentation
open DaggerAmalgamUnitBoundary DaggerAmalgamPaddedClassifier
open DaggerAmalgamRankFiltration

universe u

set_option autoImplicit false

namespace DaggerAmalgamSuccessor

noncomputable section

variable (C B : SimplicialCat.{u, u}) (x : C.Obj) (b : B.Obj)

theorem evaluationStageOO_zero_isIso (a d : C.Obj) :
    IsIso (evaluationStageOO C B x b a d 0) := by
  apply (NatTrans.isIso_iff_isIso_app _).2
  intro q
  apply (isIso_iff_bijective _).2
  exact ((familyOO_degreeEquiv C B x b a d 0 q).trans
    (baseEquivOO C B x b q a d)).bijective

/-- The forward map is literally the original evaluation into the actual rank-zero stage. -/
def zeroStageOOIso (a d : C.Obj) :
    familyOO C B x b a d 0 ≅ (oldOldStage C B x b 0 a d : SSet.{u}) := by
  have : IsIso (evaluationStageOO C B x b a d 0) :=
    evaluationStageOO_zero_isIso C B x b a d
  exact asIso (evaluationStageOO C B x b a d 0)

theorem zeroStageOOIso_hom (a d : C.Obj) :
    (zeroStageOOIso C B x b a d).hom = evaluationStageOO C B x b a d 0 := rfl

theorem zeroStageOOIso_hom_ι (a d : C.Obj) :
    (zeroStageOOIso C B x b a d).hom ≫ (oldOldStage C B x b 0 a d).ι =
      evaluationOO C B x b a d 0 := evaluationStageOO_ι C B x b a d 0

theorem evaluationStageON_zero_isIso (a : C.Obj) (w : B.Obj) (hw : w ≠ b) :
    IsIso (evaluationStageON C B x b a w 0) := by
  apply (NatTrans.isIso_iff_isIso_app _).2
  intro q
  apply (isIso_iff_bijective _).2
  exact ((familyON_degreeEquiv C B x b a w 0 q).trans
    (baseEquivON C B x b q a w hw)).bijective

/-- The forward map is literally the original evaluation into the actual rank-zero stage. -/
def zeroStageONIso (a : C.Obj) (w : B.Obj) (hw : w ≠ b) :
    familyON C B x b a w 0 ≅ (oldNewStage C B x b 0 a w : SSet.{u}) := by
  have : IsIso (evaluationStageON C B x b a w 0) :=
    evaluationStageON_zero_isIso C B x b a w hw
  exact asIso (evaluationStageON C B x b a w 0)

theorem zeroStageONIso_hom (a : C.Obj) (w : B.Obj) (hw : w ≠ b) :
    (zeroStageONIso C B x b a w hw).hom = evaluationStageON C B x b a w 0 := rfl

theorem zeroStageONIso_hom_ι (a : C.Obj) (w : B.Obj) (hw : w ≠ b) :
    (zeroStageONIso C B x b a w hw).hom ≫ (oldNewStage C B x b 0 a w).ι =
      evaluationON C B x b a w 0 := evaluationStageON_ι C B x b a w 0

theorem evaluationStageNO_zero_isIso (z : B.Obj) (d : C.Obj) (hz : z ≠ b) :
    IsIso (evaluationStageNO C B x b z d 0) := by
  apply (NatTrans.isIso_iff_isIso_app _).2
  intro q
  apply (isIso_iff_bijective _).2
  exact ((familyNO_degreeEquiv C B x b z d 0 q).trans
    (baseEquivNO C B x b q z hz d)).bijective

/-- The forward map is literally the original evaluation into the actual rank-zero stage. -/
def zeroStageNOIso (z : B.Obj) (d : C.Obj) (hz : z ≠ b) :
    familyNO C B x b z d 0 ≅ (newOldStage C B x b 0 z d : SSet.{u}) := by
  have : IsIso (evaluationStageNO C B x b z d 0) :=
    evaluationStageNO_zero_isIso C B x b z d hz
  exact asIso (evaluationStageNO C B x b z d 0)

theorem zeroStageNOIso_hom (z : B.Obj) (d : C.Obj) (hz : z ≠ b) :
    (zeroStageNOIso C B x b z d hz).hom = evaluationStageNO C B x b z d 0 := rfl

theorem zeroStageNOIso_hom_ι (z : B.Obj) (d : C.Obj) (hz : z ≠ b) :
    (zeroStageNOIso C B x b z d hz).hom ≫ (newOldStage C B x b 0 z d).ι =
      evaluationNO C B x b z d 0 := evaluationStageNO_ι C B x b z d 0

theorem evaluationStageNN_zero_isIso (z w : B.Obj) (hz : z ≠ b) (hw : w ≠ b) :
    IsIso (evaluationStageNN C B x b z w 0) := by
  apply (NatTrans.isIso_iff_isIso_app _).2
  intro q
  apply (isIso_iff_bijective _).2
  exact ((familyNN_degreeEquiv C B x b z w 0 q).trans
    (baseEquivNN C B x b q z w hz hw)).bijective

/-- The forward map is literally the original evaluation into the actual rank-zero stage. -/
def zeroStageNNIso (z w : B.Obj) (hz : z ≠ b) (hw : w ≠ b) :
    familyNN C B x b z w 0 ≅ (newNewStage C B x b 0 z w : SSet.{u}) := by
  have : IsIso (evaluationStageNN C B x b z w 0) :=
    evaluationStageNN_zero_isIso C B x b z w hz hw
  exact asIso (evaluationStageNN C B x b z w 0)

theorem zeroStageNNIso_hom (z w : B.Obj) (hz : z ≠ b) (hw : w ≠ b) :
    (zeroStageNNIso C B x b z w hz hw).hom = evaluationStageNN C B x b z w 0 := rfl

theorem zeroStageNNIso_hom_ι (z w : B.Obj) (hz : z ≠ b) (hw : w ≠ b) :
    (zeroStageNNIso C B x b z w hz hw).hom ≫ (newNewStage C B x b 0 z w).ι =
      evaluationNN C B x b z w 0 := evaluationStageNN_ι C B x b z w 0

end
end DaggerAmalgamSuccessor
