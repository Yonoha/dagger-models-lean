import OriginalFlagP2BidegreeReconciledRecovered
import ChosenNecklaceOuterFlags
import NerveHomotopy
import OriginalRecoveredClosedExpressionApplication
import OriginalRecoveredBoundaryProductReconciliationData

/-! Original OriginalFlagP2FlagCollapse, with unchanged closed types and values. -/

set_option autoImplicit false
set_option maxRecDepth 100000

noncomputable def DaggerOriginalFlagFlankification.outerCollapse.{u, u_1}
    (arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredBoundaryProductReconciliationData.jsonData 17003
        [])
    :
    recovered_closed_result_type%
      DaggerRecoveredBoundaryProductReconciliationData.jsonData 17003
      [arg0]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredBoundaryProductReconciliationData.jsonData 17003 :=
    @(recovered_closed_expr%
      DaggerRecoveredBoundaryProductReconciliationData.jsonData 17025)
  exact @f arg0

noncomputable def DaggerOriginalFlagFlankification.flagCollapse.{u}
    (arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredBoundaryProductReconciliationData.jsonData 17179
        [])
    :
    recovered_closed_result_type%
      DaggerRecoveredBoundaryProductReconciliationData.jsonData 17179
      [arg0]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredBoundaryProductReconciliationData.jsonData 17179 :=
    @(recovered_closed_expr%
      DaggerRecoveredBoundaryProductReconciliationData.jsonData 17213)
  exact @f arg0

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerOriginalFlagFlankification.flagCollapse.eq_1)
  pure ()

theorem DaggerOriginalFlagFlankification.outerTop._proof_1.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredBoundaryProductReconciliationData.jsonData 17102 :=
  @(recovered_closed_expr%
    DaggerRecoveredBoundaryProductReconciliationData.jsonData 17106)

theorem DaggerOriginalFlagFlankification.outerTop._proof_2.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredBoundaryProductReconciliationData.jsonData 17164 :=
  @(recovered_closed_expr%
    DaggerRecoveredBoundaryProductReconciliationData.jsonData 17166)

theorem DaggerOriginalFlagFlankification.outerTop._proof_3 :
  recovered_closed_expr%
    DaggerRecoveredBoundaryProductReconciliationData.jsonData 17168 :=
  @(recovered_closed_expr%
    DaggerRecoveredBoundaryProductReconciliationData.jsonData 17172)

theorem DaggerOriginalFlagFlankification.outerTop._proof_4.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredBoundaryProductReconciliationData.jsonData 17138 :=
  @(recovered_closed_expr%
    DaggerRecoveredBoundaryProductReconciliationData.jsonData 17147)

theorem DaggerOriginalFlagFlankification.outerTop._proof_5.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredBoundaryProductReconciliationData.jsonData 17154 :=
  @(recovered_closed_expr%
    DaggerRecoveredBoundaryProductReconciliationData.jsonData 17160)

theorem DaggerOriginalFlagFlankification.outerTop._proof_6.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredBoundaryProductReconciliationData.jsonData 17550 :=
  @(recovered_closed_expr%
    DaggerRecoveredBoundaryProductReconciliationData.jsonData 17557)

noncomputable def DaggerOriginalFlagFlankification.outerTop.{u}
    (arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredBoundaryProductReconciliationData.jsonData 17795
        [])
    :
    recovered_closed_result_type%
      DaggerRecoveredBoundaryProductReconciliationData.jsonData 17795
      [arg0]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredBoundaryProductReconciliationData.jsonData 17795 :=
    @(recovered_closed_expr%
      DaggerRecoveredBoundaryProductReconciliationData.jsonData 17831)
  exact @f arg0

noncomputable def DaggerOriginalFlagFlankification.outerCenter.{u, u_1}
    (arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredBoundaryProductReconciliationData.jsonData 17340
        [])
    :
    recovered_closed_result_type%
      DaggerRecoveredBoundaryProductReconciliationData.jsonData 17340
      [arg0]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredBoundaryProductReconciliationData.jsonData 17340 :=
    @(recovered_closed_expr%
      DaggerRecoveredBoundaryProductReconciliationData.jsonData 17359)
  exact @f arg0

theorem DaggerOriginalFlagFlankification.outerToTop._proof_1.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredBoundaryProductReconciliationData.jsonData 17789 :=
  @(recovered_closed_expr%
    DaggerRecoveredBoundaryProductReconciliationData.jsonData 17794)

noncomputable def DaggerOriginalFlagFlankification.outerToTop.{u}
    (arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredBoundaryProductReconciliationData.jsonData 17227
        [])
    (arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredBoundaryProductReconciliationData.jsonData 17227
        [arg0])
    :
    recovered_closed_result_type%
      DaggerRecoveredBoundaryProductReconciliationData.jsonData 17227
      [arg0, arg1]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredBoundaryProductReconciliationData.jsonData 17227 :=
    @(recovered_closed_expr%
      DaggerRecoveredBoundaryProductReconciliationData.jsonData 17334)
  exact @f arg0 arg1

theorem DaggerOriginalFlagFlankification.outerToCenter._proof_1.{u_1, u_2} :
  recovered_closed_expr%
    DaggerRecoveredBoundaryProductReconciliationData.jsonData 17704 :=
  @(recovered_closed_expr%
    DaggerRecoveredBoundaryProductReconciliationData.jsonData 17766)

noncomputable def DaggerOriginalFlagFlankification.outerToCenter.{u, u_1}
    (arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredBoundaryProductReconciliationData.jsonData 17059
        [])
    :
    recovered_closed_result_type%
      DaggerRecoveredBoundaryProductReconciliationData.jsonData 17059
      [arg0]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredBoundaryProductReconciliationData.jsonData 17059 :=
    @(recovered_closed_expr%
      DaggerRecoveredBoundaryProductReconciliationData.jsonData 17075)
  exact @f arg0

theorem DaggerOriginalFlagFlankification.outerCenterToId._proof_1.{u_1, u_2} :
  recovered_closed_expr%
    DaggerRecoveredBoundaryProductReconciliationData.jsonData 17432 :=
  @(recovered_closed_expr%
    DaggerRecoveredBoundaryProductReconciliationData.jsonData 17445)

noncomputable def DaggerOriginalFlagFlankification.outerCenterToId.{u_1, u_2}
    (arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredBoundaryProductReconciliationData.jsonData 17458
        [])
    :
    recovered_closed_result_type%
      DaggerRecoveredBoundaryProductReconciliationData.jsonData 17458
      [arg0]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredBoundaryProductReconciliationData.jsonData 17458 :=
    @(recovered_closed_expr%
      DaggerRecoveredBoundaryProductReconciliationData.jsonData 17484)
  exact @f arg0

theorem DaggerOriginalFlagFlankification.outerCollapse_geometricW.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredBoundaryProductReconciliationData.jsonData 16868 :=
  @(recovered_closed_expr%
    DaggerRecoveredBoundaryProductReconciliationData.jsonData 16993)

theorem DaggerOriginalFlagFlankification.flagCollapse_geometricW.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredBoundaryProductReconciliationData.jsonData 16611 :=
  @(recovered_closed_expr%
    DaggerRecoveredBoundaryProductReconciliationData.jsonData 16854)

