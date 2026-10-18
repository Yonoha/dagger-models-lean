import OriginalRLPFunctorsRecovered
import OriginalRecoveredClosedExpressionApplication
import OriginalRecoveredRLPAccessibilityPipelineData

/-! Original RLPArrowColimits, with unchanged closed types and values. -/

set_option autoImplicit false
set_option maxRecDepth 100000

theorem DaggerRLPAccessibility.arrowIsColimit._proof_1.{u_1, u_2, u_3, u_4} :
  recovered_closed_expr%
    DaggerRecoveredRLPAccessibilityPipelineData.jsonData 39797 :=
  @(recovered_closed_expr%
    DaggerRecoveredRLPAccessibilityPipelineData.jsonData 39831)

theorem DaggerRLPAccessibility.arrowIsColimit._proof_2.{u_1, u_2, u_3, u_4} :
  recovered_closed_expr%
    DaggerRecoveredRLPAccessibilityPipelineData.jsonData 37928 :=
  @(recovered_closed_expr%
    DaggerRecoveredRLPAccessibilityPipelineData.jsonData 38548)

theorem DaggerRLPAccessibility.arrowIsColimit._proof_3.{u_1, u_2, u_3, u_4} :
  recovered_closed_expr%
    DaggerRecoveredRLPAccessibilityPipelineData.jsonData 38635 :=
  @(recovered_closed_expr%
    DaggerRecoveredRLPAccessibilityPipelineData.jsonData 38722)

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `CategoryTheory.Comma.coconeOfPreserves.eq_1)
  pure ()

theorem DaggerRLPAccessibility.arrowIsColimit._proof_4.{u_1, u_2, u_3, u_4} :
  recovered_closed_expr%
    DaggerRecoveredRLPAccessibilityPipelineData.jsonData 39957 :=
  @(recovered_closed_expr%
    DaggerRecoveredRLPAccessibilityPipelineData.jsonData 40284)

noncomputable def DaggerRLPAccessibility.arrowIsColimit.{v, u, t, s}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredRLPAccessibilityPipelineData.jsonData 40361
        []}
    [arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredRLPAccessibilityPipelineData.jsonData 40361
        [arg0]]
    {arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredRLPAccessibilityPipelineData.jsonData 40361
        [arg0, arg1]}
    [arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredRLPAccessibilityPipelineData.jsonData 40361
        [arg0, arg1, arg2]]
    {arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredRLPAccessibilityPipelineData.jsonData 40361
        [arg0, arg1, arg2, arg3]}
    (arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredRLPAccessibilityPipelineData.jsonData 40361
        [arg0, arg1, arg2, arg3, arg4])
    (arg6 :
      recovered_closed_binder_type%
        DaggerRecoveredRLPAccessibilityPipelineData.jsonData 40361
        [arg0, arg1, arg2, arg3, arg4, arg5])
    (arg7 :
      recovered_closed_binder_type%
        DaggerRecoveredRLPAccessibilityPipelineData.jsonData 40361
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6])
    :
    recovered_closed_result_type%
      DaggerRecoveredRLPAccessibilityPipelineData.jsonData 40361
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredRLPAccessibilityPipelineData.jsonData 40361 :=
    @(recovered_closed_expr%
      DaggerRecoveredRLPAccessibilityPipelineData.jsonData 40675)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5 arg6 arg7

theorem DaggerRLPAccessibility.liftFunctor_accessible.{w, v, u, t} :
  recovered_closed_expr%
    DaggerRecoveredRLPAccessibilityPipelineData.jsonData 39468 :=
  @(recovered_closed_expr%
    DaggerRecoveredRLPAccessibilityPipelineData.jsonData 39733)

