import OriginalProductBeadNerveCollapse
import OriginalFlagP2CompleteReconciledRecovered
import OriginalFlagP2FlagCollapseReconciledRecovered
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import OriginalRecoveredClosedExpressionApplication
import OriginalRecoveredBoundaryProductReconciliationData

/-! Original OriginalProductBeadFlagCollapse, with unchanged closed types and values. -/

set_option autoImplicit false
set_option maxRecDepth 100000

noncomputable def DaggerOriginalProductGadget.beadNerveCollapsePoint.{u}
    (arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredBoundaryProductReconciliationData.jsonData 23943
        [])
    (arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredBoundaryProductReconciliationData.jsonData 23943
        [arg0])
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredBoundaryProductReconciliationData.jsonData 23943
        [arg0, arg1])
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredBoundaryProductReconciliationData.jsonData 23943
        [arg0, arg1, arg2])
    :
    recovered_closed_result_type%
      DaggerRecoveredBoundaryProductReconciliationData.jsonData 23943
      [arg0, arg1, arg2, arg3]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredBoundaryProductReconciliationData.jsonData 23943 :=
    @(recovered_closed_expr%
      DaggerRecoveredBoundaryProductReconciliationData.jsonData 23947)
  exact @f arg0 arg1 arg2 arg3

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerOriginalProductGadget.beadNerveCollapsePoint.eq_1)
  pure ()

theorem DaggerOriginalProductGadget.beadNerveCollapsePoint_GW.{u} :
  recovered_closed_expr%
    DaggerRecoveredBoundaryProductReconciliationData.jsonData 23722 :=
  @(recovered_closed_expr%
    DaggerRecoveredBoundaryProductReconciliationData.jsonData 23880)

theorem DaggerOriginalProductGadget.pointMap._proof_1.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredBoundaryProductReconciliationData.jsonData 23912 :=
  @(recovered_closed_expr%
    DaggerRecoveredBoundaryProductReconciliationData.jsonData 23939)

noncomputable def DaggerOriginalProductGadget.pointMap.{u}
    (arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredBoundaryProductReconciliationData.jsonData 24035
        [])
    :
    recovered_closed_result_type%
      DaggerRecoveredBoundaryProductReconciliationData.jsonData 24035
      [arg0]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredBoundaryProductReconciliationData.jsonData 24035 :=
    @(recovered_closed_expr%
      DaggerRecoveredBoundaryProductReconciliationData.jsonData 24045)
  exact @f arg0

theorem DaggerOriginalProductGadget.pointIsTerminal._proof_1.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredBoundaryProductReconciliationData.jsonData 23957 :=
  @(recovered_closed_expr%
    DaggerRecoveredBoundaryProductReconciliationData.jsonData 24032)

noncomputable def DaggerOriginalProductGadget.pointIsTerminal.{u_1}
    :
    recovered_closed_result_type%
      DaggerRecoveredBoundaryProductReconciliationData.jsonData 24049
      []
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredBoundaryProductReconciliationData.jsonData 24049 :=
    @(recovered_closed_expr%
      DaggerRecoveredBoundaryProductReconciliationData.jsonData 24056)
  exact @f

theorem DaggerOriginalProductGadget.beadFlagHomCollapse_GW.{u} :
  recovered_closed_expr%
    DaggerRecoveredBoundaryProductReconciliationData.jsonData 24069 :=
  @(recovered_closed_expr%
    DaggerRecoveredBoundaryProductReconciliationData.jsonData 24299)

