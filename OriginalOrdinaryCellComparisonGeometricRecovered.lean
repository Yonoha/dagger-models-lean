import OriginalOrdinaryCellComparisonBoundaryGeometricRecovered
import FilteredGeometric
import SimplicialIsoHoms
import OriginalRecoveredClosedExpressionApplication
import OriginalRecoveredGlobalLeftProperData

/-! Original OrdinaryCellComparisonGeometric, with unchanged closed types and values. -/

set_option autoImplicit false
set_option maxRecDepth 100000

theorem DaggerOrdinaryCellComparisonGeometric.StageF_geometric._simp_1_1.{v, u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 24280 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 24302)

theorem DaggerOrdinaryCellComparisonGeometric.StageF_geometric.{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 178931 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 179601)

theorem DaggerOrdinaryCellComparisonGeometric.QF_map_geometric.{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 178346 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 178801)

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerOrdinaryCellComparisonData.StageF.congr_simp)
  pure ()

theorem DaggerOrdinaryCellComparisonGeometric.imageQF_map_geometric.{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 179696 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 179734)

theorem DaggerOrdinaryCellComparisonGeometric.ordinary_cell_comparison_geometric.{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 179898 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 180209)

