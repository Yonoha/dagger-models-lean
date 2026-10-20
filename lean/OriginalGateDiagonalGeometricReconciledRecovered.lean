import OriginalGateBisimplicial
import OriginalDiagonalGeometricReconciledRecovered
import OriginalRecoveredClosedExpressionApplication
import OriginalRecoveredBoundaryProductReconciliationData

/-! Original OriginalGateDiagonalGeometric, with unchanged closed types and values. -/

set_option autoImplicit false
set_option maxRecDepth 100000

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerOriginalProductGadget.gateOuterAugmentation.eq_1)
  pure ()

theorem DaggerOriginalProductGadget.gateOuterEta_row_GW.{u} :
  recovered_closed_expr%
    DaggerRecoveredBoundaryProductReconciliationData.jsonData 57855 :=
  @(recovered_closed_expr%
    DaggerRecoveredBoundaryProductReconciliationData.jsonData 58048)

theorem DaggerOriginalProductGadget.gateDiagonalAugmentation_GW.{u} :
  recovered_closed_expr%
    DaggerRecoveredBoundaryProductReconciliationData.jsonData 57787 :=
  @(recovered_closed_expr%
    DaggerRecoveredBoundaryProductReconciliationData.jsonData 57817)

theorem DaggerOriginalProductGadget.productGateDiagonalAugmentation_GW.{u} :
  recovered_closed_expr%
    DaggerRecoveredBoundaryProductReconciliationData.jsonData 58186 :=
  @(recovered_closed_expr%
    DaggerRecoveredBoundaryProductReconciliationData.jsonData 58293)

