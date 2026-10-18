import OriginalActualCoherentUnitaryIdentityRecovered
import OriginalActualGlobalWeakDefinitionsRecovered
import OriginalActualGlobalWeakPropertiesRecovered
import OriginalUnitaryCompositionUnifiedRecovered
import OriginalAmalgamTranslationCollapseRecovered
import OriginalRecoveredClosedExpressionApplication
import OriginalRecoveredGlobalModelEndpointSupportData

/-! Original DKEndpointTransport, with unchanged closed types and values. -/

set_option autoImplicit false
set_option maxRecDepth 100000

theorem DaggerGlobalDKClosure.transport._proof_1.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredGlobalModelEndpointSupportData.jsonData 1731 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalModelEndpointSupportData.jsonData 1792)

noncomputable def DaggerGlobalDKClosure.transport.{u}
    (arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalModelEndpointSupportData.jsonData 1803
        [])
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalModelEndpointSupportData.jsonData 1803
        [arg0]}
    {arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalModelEndpointSupportData.jsonData 1803
        [arg0, arg1]}
    {arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalModelEndpointSupportData.jsonData 1803
        [arg0, arg1, arg2]}
    {arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalModelEndpointSupportData.jsonData 1803
        [arg0, arg1, arg2, arg3]}
    (arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalModelEndpointSupportData.jsonData 1803
        [arg0, arg1, arg2, arg3, arg4])
    (arg6 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalModelEndpointSupportData.jsonData 1803
        [arg0, arg1, arg2, arg3, arg4, arg5])
    :
    recovered_closed_result_type%
      DaggerRecoveredGlobalModelEndpointSupportData.jsonData 1803
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredGlobalModelEndpointSupportData.jsonData 1803 :=
    @(recovered_closed_expr%
      DaggerRecoveredGlobalModelEndpointSupportData.jsonData 1824)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5 arg6

theorem DaggerGlobalDKClosure.map_of_eq.{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalModelEndpointSupportData.jsonData 151 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalModelEndpointSupportData.jsonData 460)

theorem DaggerGlobalDKClosure.coherentlyUnitary_transport.{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalModelEndpointSupportData.jsonData 514 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalModelEndpointSupportData.jsonData 838)

theorem DaggerGlobalDKClosure.transport_comp.{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalModelEndpointSupportData.jsonData 903 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalModelEndpointSupportData.jsonData 1681)

theorem DaggerGlobalDKClosure.transport_map.{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalModelEndpointSupportData.jsonData 1903 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalModelEndpointSupportData.jsonData 1925)

theorem DaggerGlobalDKClosure.transport_refl.{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalModelEndpointSupportData.jsonData 1950 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalModelEndpointSupportData.jsonData 1955)

theorem DaggerGlobalDKClosure.local_geometric_iff.{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalModelEndpointSupportData.jsonData 2010 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalModelEndpointSupportData.jsonData 2081)

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerGlobalDKClosure.transport.congr_simp)
  pure ()

