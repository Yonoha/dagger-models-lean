import OriginalProductCrossingGateIndexReconciledRecovered
import OriginalRecoveredClosedExpressionApplication
import OriginalRecoveredBoundaryProductReconciliationData

/-! Original OriginalProductIntervalVertices, with unchanged closed types and values. -/

set_option autoImplicit false
set_option maxRecDepth 100000

theorem DaggerOriginalProductGadget.productIntervalVertex._proof_1.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredBoundaryProductReconciliationData.jsonData 60946 :=
  @(recovered_closed_expr%
    DaggerRecoveredBoundaryProductReconciliationData.jsonData 60949)

theorem DaggerOriginalProductGadget.productIntervalVertex._proof_2.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredBoundaryProductReconciliationData.jsonData 62652 :=
  @(recovered_closed_expr%
    DaggerRecoveredBoundaryProductReconciliationData.jsonData 62666)

noncomputable def DaggerOriginalProductGadget.productIntervalVertex.{u}
    (arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredBoundaryProductReconciliationData.jsonData 61388
        [])
    (arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredBoundaryProductReconciliationData.jsonData 61388
        [arg0])
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredBoundaryProductReconciliationData.jsonData 61388
        [arg0, arg1])
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredBoundaryProductReconciliationData.jsonData 61388
        [arg0, arg1, arg2])
    (arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredBoundaryProductReconciliationData.jsonData 61388
        [arg0, arg1, arg2, arg3])
    (arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredBoundaryProductReconciliationData.jsonData 61388
        [arg0, arg1, arg2, arg3, arg4])
    (arg6 :
      recovered_closed_binder_type%
        DaggerRecoveredBoundaryProductReconciliationData.jsonData 61388
        [arg0, arg1, arg2, arg3, arg4, arg5])
    (arg7 :
      recovered_closed_binder_type%
        DaggerRecoveredBoundaryProductReconciliationData.jsonData 61388
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6])
    :
    recovered_closed_result_type%
      DaggerRecoveredBoundaryProductReconciliationData.jsonData 61388
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredBoundaryProductReconciliationData.jsonData 61388 :=
    @(recovered_closed_expr%
      DaggerRecoveredBoundaryProductReconciliationData.jsonData 61405)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5 arg6 arg7

theorem DaggerOriginalProductGadget.productIntervalVertex_fst.{u} :
  recovered_closed_expr%
    DaggerRecoveredBoundaryProductReconciliationData.jsonData 61110 :=
  @(recovered_closed_expr%
    DaggerRecoveredBoundaryProductReconciliationData.jsonData 61191)

theorem DaggerOriginalProductGadget.productIntervalInclusion_fst.{u} :
  recovered_closed_expr%
    DaggerRecoveredBoundaryProductReconciliationData.jsonData 61644 :=
  @(recovered_closed_expr%
    DaggerRecoveredBoundaryProductReconciliationData.jsonData 61741)

theorem DaggerOriginalProductGadget.productIntervalInclusion_coordinate.{u} :
  recovered_closed_expr%
    DaggerRecoveredBoundaryProductReconciliationData.jsonData 62315 :=
  @(recovered_closed_expr%
    DaggerRecoveredBoundaryProductReconciliationData.jsonData 62615)

theorem DaggerOriginalProductGadget.productIntervalInclusion_le_iff._simp_1_1.{u_2, u_3} :
  recovered_closed_expr%
    DaggerRecoveredBoundaryProductReconciliationData.jsonData 62258 :=
  @(recovered_closed_expr%
    DaggerRecoveredBoundaryProductReconciliationData.jsonData 62276)

theorem DaggerOriginalProductGadget.productIntervalInclusion_le_iff.{u} :
  recovered_closed_expr%
    DaggerRecoveredBoundaryProductReconciliationData.jsonData 62005 :=
  @(recovered_closed_expr%
    DaggerRecoveredBoundaryProductReconciliationData.jsonData 62201)

theorem DaggerOriginalProductGadget.productNecklaceVertex_ext.{u} :
  recovered_closed_expr%
    DaggerRecoveredBoundaryProductReconciliationData.jsonData 62690 :=
  @(recovered_closed_expr%
    DaggerRecoveredBoundaryProductReconciliationData.jsonData 62922)

theorem DaggerOriginalProductGadget.productIntervalVertex_fac.{u} :
  recovered_closed_expr%
    DaggerRecoveredBoundaryProductReconciliationData.jsonData 61769 :=
  @(recovered_closed_expr%
    DaggerRecoveredBoundaryProductReconciliationData.jsonData 61943)

theorem DaggerOriginalProductGadget.productIntervalVertex_le.{u} :
  recovered_closed_expr%
    DaggerRecoveredBoundaryProductReconciliationData.jsonData 61276 :=
  @(recovered_closed_expr%
    DaggerRecoveredBoundaryProductReconciliationData.jsonData 61378)

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerOriginalProductGadget.productIntervalVertex.congr_simp)
  pure ()

