import PushoutRetract
import OriginalGlobalModelDataRecovered
import Mathlib.CategoryTheory.SmallObject.Basic
import OriginalRecoveredClosedExpressionApplication
import OriginalRecoveredGlobalLeftProperData

/-! Original CofibrationSOA, with unchanged closed types and values. -/

set_option autoImplicit false
set_option maxRecDepth 100000

noncomputable abbrev DaggerCofibrationPushoutRetract.G.{u}
    :
    recovered_closed_result_type%
      DaggerRecoveredGlobalLeftProperData.jsonData 8279
      []
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 8279 :=
    @(recovered_closed_expr%
      DaggerRecoveredGlobalLeftProperData.jsonData 57)
  exact @f

noncomputable abbrev DaggerCofibrationPushoutRetract.I.{u}
    :
    recovered_closed_result_type%
      DaggerRecoveredGlobalLeftProperData.jsonData 5622
      []
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 5622 :=
    @(recovered_closed_expr%
      DaggerRecoveredGlobalLeftProperData.jsonData 187226)
  exact @f

theorem DaggerCofibrationPushoutRetract.instHasSmallObjectArgumentDaggerSimplicialCatI.{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 188162 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 188163)

noncomputable abbrev DaggerCofibrationPushoutRetract.soaCardinal.{u}
    :
    recovered_closed_result_type%
      DaggerRecoveredGlobalLeftProperData.jsonData 188559
      []
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 188559 :=
    @(recovered_closed_expr%
      DaggerRecoveredGlobalLeftProperData.jsonData 188792)
  exact @f

theorem DaggerCofibrationPushoutRetract.soaRegular.{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 188556 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 188634)

theorem
DaggerCofibrationPushoutRetract.instIsCardinalForSmallObjectArgumentDaggerSimplicialCatISoaCardinal
    .{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 189144 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 189155)

noncomputable def DaggerCofibrationPushoutRetract.soaObj.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 189222
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 189222
        [arg0]}
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 189222
        [arg0, arg1])
    :
    recovered_closed_result_type%
      DaggerRecoveredGlobalLeftProperData.jsonData 189222
      [arg0, arg1, arg2]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 189222 :=
    @(recovered_closed_expr%
      DaggerRecoveredGlobalLeftProperData.jsonData 189236)
  exact @f arg0 arg1 arg2

noncomputable def DaggerCofibrationPushoutRetract.soaLeft.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 188167
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 188167
        [arg0]}
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 188167
        [arg0, arg1])
    :
    recovered_closed_result_type%
      DaggerRecoveredGlobalLeftProperData.jsonData 188167
      [arg0, arg1, arg2]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 188167 :=
    @(recovered_closed_expr%
      DaggerRecoveredGlobalLeftProperData.jsonData 188181)
  exact @f arg0 arg1 arg2

noncomputable def DaggerCofibrationPushoutRetract.soaCell.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 188896
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 188896
        [arg0]}
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 188896
        [arg0, arg1])
    :
    recovered_closed_result_type%
      DaggerRecoveredGlobalLeftProperData.jsonData 188896
      [arg0, arg1, arg2]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 188896 :=
    @(recovered_closed_expr%
      DaggerRecoveredGlobalLeftProperData.jsonData 188899)
  exact @f arg0 arg1 arg2

theorem DaggerCofibrationPushoutRetract.soaCell_original.{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 187857 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 187862)

noncomputable def DaggerCofibrationPushoutRetract.soaRight.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 188538
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 188538
        [arg0]}
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 188538
        [arg0, arg1])
    :
    recovered_closed_result_type%
      DaggerRecoveredGlobalLeftProperData.jsonData 188538
      [arg0, arg1, arg2]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 188538 :=
    @(recovered_closed_expr%
      DaggerRecoveredGlobalLeftProperData.jsonData 188552)
  exact @f arg0 arg1 arg2

theorem DaggerCofibrationPushoutRetract.soa_fac.{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 188144 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 188158)

theorem DaggerCofibrationPushoutRetract.soaRight_mem.{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 188422 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 188436)

theorem DaggerCofibrationPushoutRetract.sameSourceRetract._proof_1.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 188404 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 188416)

noncomputable def DaggerCofibrationPushoutRetract.sameSourceRetract.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 188103
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 188103
        [arg0]}
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 188103
        [arg0, arg1])
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 188103
        [arg0, arg1, arg2])
    :
    recovered_closed_result_type%
      DaggerRecoveredGlobalLeftProperData.jsonData 188103
      [arg0, arg1, arg2, arg3]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 188103 :=
    @(recovered_closed_expr%
      DaggerRecoveredGlobalLeftProperData.jsonData 188127)
  exact @f arg0 arg1 arg2 arg3

noncomputable def DaggerCofibrationPushoutRetract.soaLift.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 188638
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 188638
        [arg0]}
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 188638
        [arg0, arg1])
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 188638
        [arg0, arg1, arg2])
    :
    recovered_closed_result_type%
      DaggerRecoveredGlobalLeftProperData.jsonData 188638
      [arg0, arg1, arg2, arg3]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 188638 :=
    @(recovered_closed_expr%
      DaggerRecoveredGlobalLeftProperData.jsonData 188654)
  exact @f arg0 arg1 arg2 arg3

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerCofibrationPushoutRetract.soaLift.congr_simp)
  pure ()

theorem DaggerCofibrationPushoutRetract.sameSourceRetract_r_left.{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 187959 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 187965)

noncomputable def DaggerCofibrationPushoutRetract.chosenModelData.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 188902
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 188902
        [arg0]}
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 188902
        [arg0, arg1])
    :
    recovered_closed_result_type%
      DaggerRecoveredGlobalLeftProperData.jsonData 188902
      [arg0, arg1, arg2]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 188902 :=
    @(recovered_closed_expr%
      DaggerRecoveredGlobalLeftProperData.jsonData 188905)
  exact @f arg0 arg1 arg2

theorem DaggerCofibrationPushoutRetract.chosenModelRetract._proof_1.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 188020 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 188031)

theorem DaggerCofibrationPushoutRetract.chosenModelRetract._proof_2.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 188466 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 188483)

noncomputable def DaggerCofibrationPushoutRetract.chosenModelRetract.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 188064
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 188064
        [arg0]}
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 188064
        [arg0, arg1])
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 188064
        [arg0, arg1, arg2])
    :
    recovered_closed_result_type%
      DaggerRecoveredGlobalLeftProperData.jsonData 188064
      [arg0, arg1, arg2, arg3]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 188064 :=
    @(recovered_closed_expr%
      DaggerRecoveredGlobalLeftProperData.jsonData 188096)
  exact @f arg0 arg1 arg2 arg3

theorem DaggerCofibrationPushoutRetract.sameSourceRetract_i_left.{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 188199 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 188205)

noncomputable def DaggerCofibrationPushoutRetract.soaSquare.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 188220
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 188220
        [arg0]}
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 188220
        [arg0, arg1])
    :
    recovered_closed_result_type%
      DaggerRecoveredGlobalLeftProperData.jsonData 188220
      [arg0, arg1, arg2]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 188220 :=
    @(recovered_closed_expr%
      DaggerRecoveredGlobalLeftProperData.jsonData 188273)
  exact @f arg0 arg1 arg2

theorem DaggerCofibrationPushoutRetract.chosenModelData_original.{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 188293 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 188298)

theorem DaggerCofibrationPushoutRetract.chosenModel_Z.{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 188335 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 188344)

theorem DaggerCofibrationPushoutRetract.chosenModel_i.{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 188371 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 188380)

noncomputable def DaggerCofibrationPushoutRetract.soaHasPushouts.{u}
    :
    recovered_closed_result_type%
      DaggerRecoveredGlobalLeftProperData.jsonData 188439
      []
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 188439 :=
    @(recovered_closed_expr%
      DaggerRecoveredGlobalLeftProperData.jsonData 188447)
  exact @f

theorem DaggerCofibrationPushoutRetract.soaLift_left.{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 188995 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 189111)

theorem DaggerCofibrationPushoutRetract.soaLift_right.{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 188773 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 188787)

noncomputable def DaggerCofibrationPushoutRetract.soaLiftStruct.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 188504
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 188504
        [arg0]}
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 188504
        [arg0, arg1])
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 188504
        [arg0, arg1, arg2])
    :
    recovered_closed_result_type%
      DaggerRecoveredGlobalLeftProperData.jsonData 188504
      [arg0, arg1, arg2, arg3]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 188504 :=
    @(recovered_closed_expr%
      DaggerRecoveredGlobalLeftProperData.jsonData 188533)
  exact @f arg0 arg1 arg2 arg3

theorem DaggerCofibrationPushoutRetract.soaLift_right_assoc.{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 188687 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 188765)

theorem DaggerCofibrationPushoutRetract.soaLift_left_assoc.{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 188821 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 188893)

theorem DaggerCofibrationPushoutRetract.soa_fac_assoc.{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 188932 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 188987)

theorem DaggerCofibrationPushoutRetract.chosenModel_p.{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 189132 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 189141)

theorem DaggerCofibrationPushoutRetract.soaLift_eq_chosen.{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 189194 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 189200)

theorem DaggerCofibrationPushoutRetract.sameSourceRetract_r_right.{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 189213 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 189219)

