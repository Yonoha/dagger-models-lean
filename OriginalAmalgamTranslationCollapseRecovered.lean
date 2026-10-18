import AmalgamCollapseHoms
import AmalgamLowRankProducts
import OriginalCountableExtractionBasicRecovered
import OriginalRecoveredClosedExpressionApplication
import OriginalRecoveredAmalgamUnitaryBridgeData

/-! Original AmalgamTranslationCollapse, with unchanged closed types and values. -/

set_option autoImplicit false
set_option maxRecDepth 100000

noncomputable abbrev DaggerAmalgamTranslationCollapse.HomQ.{u}
    (arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredAmalgamUnitaryBridgeData.jsonData 5857
        [])
    (arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredAmalgamUnitaryBridgeData.jsonData 5857
        [arg0])
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredAmalgamUnitaryBridgeData.jsonData 5857
        [arg0, arg1])
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredAmalgamUnitaryBridgeData.jsonData 5857
        [arg0, arg1, arg2])
    (arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredAmalgamUnitaryBridgeData.jsonData 5857
        [arg0, arg1, arg2, arg3])
    (arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredAmalgamUnitaryBridgeData.jsonData 5857
        [arg0, arg1, arg2, arg3, arg4])
    :
    recovered_closed_result_type%
      DaggerRecoveredAmalgamUnitaryBridgeData.jsonData 5857
      [arg0, arg1, arg2, arg3, arg4, arg5]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredAmalgamUnitaryBridgeData.jsonData 5857 :=
    @(recovered_closed_expr%
      DaggerRecoveredAmalgamUnitaryBridgeData.jsonData 5875)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5

theorem DaggerAmalgamTranslationCollapse.glueToLeft._proof_1.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredAmalgamUnitaryBridgeData.jsonData 7577 :=
  @(recovered_closed_expr%
    DaggerRecoveredAmalgamUnitaryBridgeData.jsonData 7608)

noncomputable def DaggerAmalgamTranslationCollapse.glueToLeft.{u}
    (arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredAmalgamUnitaryBridgeData.jsonData 5774
        [])
    (arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredAmalgamUnitaryBridgeData.jsonData 5774
        [arg0])
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredAmalgamUnitaryBridgeData.jsonData 5774
        [arg0, arg1])
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredAmalgamUnitaryBridgeData.jsonData 5774
        [arg0, arg1, arg2])
    (arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredAmalgamUnitaryBridgeData.jsonData 5774
        [arg0, arg1, arg2, arg3])
    :
    recovered_closed_result_type%
      DaggerRecoveredAmalgamUnitaryBridgeData.jsonData 5774
      [arg0, arg1, arg2, arg3, arg4]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredAmalgamUnitaryBridgeData.jsonData 5774 :=
    @(recovered_closed_expr%
      DaggerRecoveredAmalgamUnitaryBridgeData.jsonData 5779)
  exact @f arg0 arg1 arg2 arg3 arg4

noncomputable def DaggerAmalgamTranslationCollapse.reverseProduct.{u}
    (arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredAmalgamUnitaryBridgeData.jsonData 4340
        [])
    (arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredAmalgamUnitaryBridgeData.jsonData 4340
        [arg0])
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredAmalgamUnitaryBridgeData.jsonData 4340
        [arg0, arg1])
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredAmalgamUnitaryBridgeData.jsonData 4340
        [arg0, arg1, arg2])
    (arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredAmalgamUnitaryBridgeData.jsonData 4340
        [arg0, arg1, arg2, arg3])
    (arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredAmalgamUnitaryBridgeData.jsonData 4340
        [arg0, arg1, arg2, arg3, arg4])
    :
    recovered_closed_result_type%
      DaggerRecoveredAmalgamUnitaryBridgeData.jsonData 4340
      [arg0, arg1, arg2, arg3, arg4, arg5]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredAmalgamUnitaryBridgeData.jsonData 4340 :=
    @(recovered_closed_expr%
      DaggerRecoveredAmalgamUnitaryBridgeData.jsonData 4354)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5

theorem DaggerAmalgamTranslationCollapse.right_collapse.{u} :
  recovered_closed_expr%
    DaggerRecoveredAmalgamUnitaryBridgeData.jsonData 5902 :=
  @(recovered_closed_expr%
    DaggerRecoveredAmalgamUnitaryBridgeData.jsonData 5915)

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerAmalgamTranslationCollapse.glueToLeft.eq_1)
  pure ()

theorem DaggerAmalgamTranslationCollapse.map_transport.{u} :
  recovered_closed_expr%
    DaggerRecoveredAmalgamUnitaryBridgeData.jsonData 6706 :=
  @(recovered_closed_expr%
    DaggerRecoveredAmalgamUnitaryBridgeData.jsonData 7566)

theorem DaggerAmalgamTranslationCollapse.glueToLeft_collapse.{u} :
  recovered_closed_expr%
    DaggerRecoveredAmalgamUnitaryBridgeData.jsonData 5518 :=
  @(recovered_closed_expr%
    DaggerRecoveredAmalgamUnitaryBridgeData.jsonData 5769)

theorem DaggerAmalgamTranslationCollapse.reverseProduct_collapse.{u} :
  recovered_closed_expr%
    DaggerRecoveredAmalgamUnitaryBridgeData.jsonData 3762 :=
  @(recovered_closed_expr%
    DaggerRecoveredAmalgamUnitaryBridgeData.jsonData 4333)

theorem DaggerAmalgamTranslationCollapse.right_same_dagger.{u} :
  recovered_closed_expr%
    DaggerRecoveredAmalgamUnitaryBridgeData.jsonData 4419 :=
  @(recovered_closed_expr%
    DaggerRecoveredAmalgamUnitaryBridgeData.jsonData 4505)

theorem DaggerAmalgamTranslationCollapse.leftToGlue._proof_1.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredAmalgamUnitaryBridgeData.jsonData 6438 :=
  @(recovered_closed_expr%
    DaggerRecoveredAmalgamUnitaryBridgeData.jsonData 6500)

noncomputable def DaggerAmalgamTranslationCollapse.leftToGlue.{u}
    (arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredAmalgamUnitaryBridgeData.jsonData 6505
        [])
    (arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredAmalgamUnitaryBridgeData.jsonData 6505
        [arg0])
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredAmalgamUnitaryBridgeData.jsonData 6505
        [arg0, arg1])
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredAmalgamUnitaryBridgeData.jsonData 6505
        [arg0, arg1, arg2])
    (arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredAmalgamUnitaryBridgeData.jsonData 6505
        [arg0, arg1, arg2, arg3])
    :
    recovered_closed_result_type%
      DaggerRecoveredAmalgamUnitaryBridgeData.jsonData 6505
      [arg0, arg1, arg2, arg3, arg4]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredAmalgamUnitaryBridgeData.jsonData 6505 :=
    @(recovered_closed_expr%
      DaggerRecoveredAmalgamUnitaryBridgeData.jsonData 6510)
  exact @f arg0 arg1 arg2 arg3 arg4

noncomputable def DaggerAmalgamTranslationCollapse.forwardProduct.{u}
    (arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredAmalgamUnitaryBridgeData.jsonData 5821
        [])
    (arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredAmalgamUnitaryBridgeData.jsonData 5821
        [arg0])
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredAmalgamUnitaryBridgeData.jsonData 5821
        [arg0, arg1])
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredAmalgamUnitaryBridgeData.jsonData 5821
        [arg0, arg1, arg2])
    (arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredAmalgamUnitaryBridgeData.jsonData 5821
        [arg0, arg1, arg2, arg3])
    (arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredAmalgamUnitaryBridgeData.jsonData 5821
        [arg0, arg1, arg2, arg3, arg4])
    :
    recovered_closed_result_type%
      DaggerRecoveredAmalgamUnitaryBridgeData.jsonData 5821
      [arg0, arg1, arg2, arg3, arg4, arg5]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredAmalgamUnitaryBridgeData.jsonData 5821 :=
    @(recovered_closed_expr%
      DaggerRecoveredAmalgamUnitaryBridgeData.jsonData 5851)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5

noncomputable def DaggerAmalgamTranslationCollapse.forward.{u}
    (arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredAmalgamUnitaryBridgeData.jsonData 5008
        [])
    (arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredAmalgamUnitaryBridgeData.jsonData 5008
        [arg0])
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredAmalgamUnitaryBridgeData.jsonData 5008
        [arg0, arg1])
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredAmalgamUnitaryBridgeData.jsonData 5008
        [arg0, arg1, arg2])
    (arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredAmalgamUnitaryBridgeData.jsonData 5008
        [arg0, arg1, arg2, arg3])
    (arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredAmalgamUnitaryBridgeData.jsonData 5008
        [arg0, arg1, arg2, arg3, arg4])
    (arg6 :
      recovered_closed_binder_type%
        DaggerRecoveredAmalgamUnitaryBridgeData.jsonData 5008
        [arg0, arg1, arg2, arg3, arg4, arg5])
    :
    recovered_closed_result_type%
      DaggerRecoveredAmalgamUnitaryBridgeData.jsonData 5008
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredAmalgamUnitaryBridgeData.jsonData 5008 :=
    @(recovered_closed_expr%
      DaggerRecoveredAmalgamUnitaryBridgeData.jsonData 5015)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5 arg6

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerAmalgamTranslationCollapse.forward.eq_1)
  pure ()

noncomputable def DaggerAmalgamTranslationCollapse.point.{u}
    (arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredAmalgamUnitaryBridgeData.jsonData 5802
        [])
    (arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredAmalgamUnitaryBridgeData.jsonData 5802
        [arg0])
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredAmalgamUnitaryBridgeData.jsonData 5802
        [arg0, arg1])
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredAmalgamUnitaryBridgeData.jsonData 5802
        [arg0, arg1, arg2])
    :
    recovered_closed_result_type%
      DaggerRecoveredAmalgamUnitaryBridgeData.jsonData 5802
      [arg0, arg1, arg2, arg3]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredAmalgamUnitaryBridgeData.jsonData 5802 :=
    @(recovered_closed_expr%
      DaggerRecoveredAmalgamUnitaryBridgeData.jsonData 5809)
  exact @f arg0 arg1 arg2 arg3

noncomputable def DaggerAmalgamTranslationCollapse.forwardStd.{u}
    (arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredAmalgamUnitaryBridgeData.jsonData 6517
        [])
    (arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredAmalgamUnitaryBridgeData.jsonData 6517
        [arg0])
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredAmalgamUnitaryBridgeData.jsonData 6517
        [arg0, arg1])
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredAmalgamUnitaryBridgeData.jsonData 6517
        [arg0, arg1, arg2])
    (arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredAmalgamUnitaryBridgeData.jsonData 6517
        [arg0, arg1, arg2, arg3])
    (arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredAmalgamUnitaryBridgeData.jsonData 6517
        [arg0, arg1, arg2, arg3, arg4])
    (arg6 :
      recovered_closed_binder_type%
        DaggerRecoveredAmalgamUnitaryBridgeData.jsonData 6517
        [arg0, arg1, arg2, arg3, arg4, arg5])
    :
    recovered_closed_result_type%
      DaggerRecoveredAmalgamUnitaryBridgeData.jsonData 6517
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredAmalgamUnitaryBridgeData.jsonData 6517 :=
    @(recovered_closed_expr%
      DaggerRecoveredAmalgamUnitaryBridgeData.jsonData 6525)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5 arg6

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerAmalgamTranslationCollapse.leftToGlue.eq_1)
  pure ()

theorem DaggerAmalgamTranslationCollapse.leftToGlue_collapse.{u} :
  recovered_closed_expr%
    DaggerRecoveredAmalgamUnitaryBridgeData.jsonData 4673 :=
  @(recovered_closed_expr%
    DaggerRecoveredAmalgamUnitaryBridgeData.jsonData 5001)

theorem DaggerAmalgamTranslationCollapse.forwardProduct_collapse.{u} :
  recovered_closed_expr%
    DaggerRecoveredAmalgamUnitaryBridgeData.jsonData 5943 :=
  @(recovered_closed_expr%
    DaggerRecoveredAmalgamUnitaryBridgeData.jsonData 6320)

theorem DaggerAmalgamTranslationCollapse.forward_collapse.{u} :
  recovered_closed_expr%
    DaggerRecoveredAmalgamUnitaryBridgeData.jsonData 5095 :=
  @(recovered_closed_expr%
    DaggerRecoveredAmalgamUnitaryBridgeData.jsonData 5270)

theorem DaggerAmalgamTranslationCollapse.forwardStd_collapse.{u} :
  recovered_closed_expr%
    DaggerRecoveredAmalgamUnitaryBridgeData.jsonData 4587 :=
  @(recovered_closed_expr%
    DaggerRecoveredAmalgamUnitaryBridgeData.jsonData 4607)

noncomputable def DaggerAmalgamTranslationCollapse.reverse.{u}
    (arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredAmalgamUnitaryBridgeData.jsonData 5484
        [])
    (arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredAmalgamUnitaryBridgeData.jsonData 5484
        [arg0])
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredAmalgamUnitaryBridgeData.jsonData 5484
        [arg0, arg1])
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredAmalgamUnitaryBridgeData.jsonData 5484
        [arg0, arg1, arg2])
    (arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredAmalgamUnitaryBridgeData.jsonData 5484
        [arg0, arg1, arg2, arg3])
    (arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredAmalgamUnitaryBridgeData.jsonData 5484
        [arg0, arg1, arg2, arg3, arg4])
    (arg6 :
      recovered_closed_binder_type%
        DaggerRecoveredAmalgamUnitaryBridgeData.jsonData 5484
        [arg0, arg1, arg2, arg3, arg4, arg5])
    :
    recovered_closed_result_type%
      DaggerRecoveredAmalgamUnitaryBridgeData.jsonData 5484
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredAmalgamUnitaryBridgeData.jsonData 5484 :=
    @(recovered_closed_expr%
      DaggerRecoveredAmalgamUnitaryBridgeData.jsonData 5491)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5 arg6

noncomputable def DaggerAmalgamTranslationCollapse.reverseStd.{u}
    (arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredAmalgamUnitaryBridgeData.jsonData 5027
        [])
    (arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredAmalgamUnitaryBridgeData.jsonData 5027
        [arg0])
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredAmalgamUnitaryBridgeData.jsonData 5027
        [arg0, arg1])
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredAmalgamUnitaryBridgeData.jsonData 5027
        [arg0, arg1, arg2])
    (arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredAmalgamUnitaryBridgeData.jsonData 5027
        [arg0, arg1, arg2, arg3])
    (arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredAmalgamUnitaryBridgeData.jsonData 5027
        [arg0, arg1, arg2, arg3, arg4])
    (arg6 :
      recovered_closed_binder_type%
        DaggerRecoveredAmalgamUnitaryBridgeData.jsonData 5027
        [arg0, arg1, arg2, arg3, arg4, arg5])
    :
    recovered_closed_result_type%
      DaggerRecoveredAmalgamUnitaryBridgeData.jsonData 5027
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredAmalgamUnitaryBridgeData.jsonData 5027 :=
    @(recovered_closed_expr%
      DaggerRecoveredAmalgamUnitaryBridgeData.jsonData 5044)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5 arg6

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerAmalgamTranslationCollapse.reverse.eq_1)
  pure ()

theorem DaggerAmalgamTranslationCollapse.reverse_collapse.{u} :
  recovered_closed_expr%
    DaggerRecoveredAmalgamUnitaryBridgeData.jsonData 5287 :=
  @(recovered_closed_expr%
    DaggerRecoveredAmalgamUnitaryBridgeData.jsonData 5477)

theorem DaggerAmalgamTranslationCollapse.reverseStd_collapse.{u} :
  recovered_closed_expr%
    DaggerRecoveredAmalgamUnitaryBridgeData.jsonData 6339 :=
  @(recovered_closed_expr%
    DaggerRecoveredAmalgamUnitaryBridgeData.jsonData 6354)

