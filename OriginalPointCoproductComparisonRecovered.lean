import OriginalPointCoproductUPRecovered
import SimplicialIsoHoms
import OriginalRecoveredClosedExpressionApplication
import OriginalRecoveredGlobalLeftProperData

/-! Original PointCoproductComparison, with unchanged closed types and values. -/

set_option autoImplicit false
set_option maxRecDepth 100000

noncomputable def DaggerPointCoproduct.extension.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 27210
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 27210
        [arg0]}
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 27210
        [arg0, arg1])
    :
    recovered_closed_result_type%
      DaggerRecoveredGlobalLeftProperData.jsonData 27210
      [arg0, arg1, arg2]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 27210 :=
    @(recovered_closed_expr%
      DaggerRecoveredGlobalLeftProperData.jsonData 27216)
  exact @f arg0 arg1 arg2

theorem DaggerPointCoproduct.extension_point.{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 25096 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 25107)

theorem DaggerPointCoproduct.extension_old.{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 25117 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 25123)

theorem DaggerPointCoproduct.extension_old_map.{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 25166 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 25229)

theorem DaggerPointCoproduct.iso_hom_map_isIso.{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 25661 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 25686)
attribute [instance] DaggerPointCoproduct.iso_hom_map_isIso

theorem DaggerPointCoproduct.local_of_precomp_iso.{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 25248 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 25638)

theorem DaggerPointCoproduct.extension_point_map.{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 25709 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 25716)

theorem DaggerPointCoproduct.emptyHomIsInitial._proof_1.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 27626 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 27670)

theorem DaggerPointCoproduct.emptyHomIsInitial._proof_2.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 27835 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 27892)

noncomputable def DaggerPointCoproduct.emptyHomIsInitial.{u}
    :
    recovered_closed_result_type%
      DaggerRecoveredGlobalLeftProperData.jsonData 25721
      []
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 25721 :=
    @(recovered_closed_expr%
      DaggerRecoveredGlobalLeftProperData.jsonData 25743)
  exact @f

theorem DaggerPointCoproduct.extension_mixed_map.{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 25757 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 25862)

theorem DaggerPointCoproduct.local_of_postcomp_iso.{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 25877 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 25977)

theorem DaggerPointCoproduct.extension_reverse_mixed_map.{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 27916 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 27989)

theorem DaggerPointCoproduct.extension_geometric.{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 25987 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 26500)

theorem DaggerPointCoproduct.comparison_conjugate.{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 26581 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 27022)

theorem DaggerPointCoproduct.original_old_obj_injective.{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 27027 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 27168)

theorem DaggerPointCoproduct.original_old_map_isIso.{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 27226 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 27585)
attribute [instance] DaggerPointCoproduct.original_old_map_isIso

theorem DaggerPointCoproduct.original_old_map_mono.{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 27173 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 27206)
attribute [instance] DaggerPointCoproduct.original_old_map_mono

theorem DaggerPointCoproduct.supplied_comparison_geometric.{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 27691 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 27805)

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerPointCoproduct.extension.eq_1)
  pure ()

