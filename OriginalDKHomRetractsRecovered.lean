import OriginalDKEndpointTransportRecovered
import OriginalRecoveredClosedExpressionApplication
import OriginalRecoveredGlobalModelEndpointSupportData

/-! Original DKHomRetracts, with unchanged closed types and values. -/

set_option autoImplicit false
set_option maxRecDepth 100000

noncomputable def DaggerGlobalDKClosure.sourceSplit.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalModelEndpointSupportData.jsonData 2205
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalModelEndpointSupportData.jsonData 2205
        [arg0]}
    {arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalModelEndpointSupportData.jsonData 2205
        [arg0, arg1]}
    {arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalModelEndpointSupportData.jsonData 2205
        [arg0, arg1, arg2]}
    {arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalModelEndpointSupportData.jsonData 2205
        [arg0, arg1, arg2, arg3]}
    {arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalModelEndpointSupportData.jsonData 2205
        [arg0, arg1, arg2, arg3, arg4]}
    (arg6 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalModelEndpointSupportData.jsonData 2205
        [arg0, arg1, arg2, arg3, arg4, arg5])
    (arg7 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalModelEndpointSupportData.jsonData 2205
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6])
    :
    recovered_closed_result_type%
      DaggerRecoveredGlobalModelEndpointSupportData.jsonData 2205
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredGlobalModelEndpointSupportData.jsonData 2205 :=
    @(recovered_closed_expr%
      DaggerRecoveredGlobalModelEndpointSupportData.jsonData 2247)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5 arg6 arg7

noncomputable def DaggerGlobalDKClosure.retractionSource.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalModelEndpointSupportData.jsonData 3101
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalModelEndpointSupportData.jsonData 3101
        [arg0]}
    {arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalModelEndpointSupportData.jsonData 3101
        [arg0, arg1]}
    {arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalModelEndpointSupportData.jsonData 3101
        [arg0, arg1, arg2]}
    {arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalModelEndpointSupportData.jsonData 3101
        [arg0, arg1, arg2, arg3]}
    {arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalModelEndpointSupportData.jsonData 3101
        [arg0, arg1, arg2, arg3, arg4]}
    (arg6 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalModelEndpointSupportData.jsonData 3101
        [arg0, arg1, arg2, arg3, arg4, arg5])
    (arg7 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalModelEndpointSupportData.jsonData 3101
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6])
    (arg8 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalModelEndpointSupportData.jsonData 3101
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7])
    :
    recovered_closed_result_type%
      DaggerRecoveredGlobalModelEndpointSupportData.jsonData 3101
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredGlobalModelEndpointSupportData.jsonData 3101 :=
    @(recovered_closed_expr%
      DaggerRecoveredGlobalModelEndpointSupportData.jsonData 3110)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5 arg6 arg7 arg8

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerGlobalDKClosure.retractionSource.eq_1)
  pure ()

noncomputable abbrev DaggerGlobalDKClosure.inclusionSource.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalModelEndpointSupportData.jsonData 3344
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalModelEndpointSupportData.jsonData 3344
        [arg0]}
    {arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalModelEndpointSupportData.jsonData 3344
        [arg0, arg1]}
    {arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalModelEndpointSupportData.jsonData 3344
        [arg0, arg1, arg2]}
    {arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalModelEndpointSupportData.jsonData 3344
        [arg0, arg1, arg2, arg3]}
    {arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalModelEndpointSupportData.jsonData 3344
        [arg0, arg1, arg2, arg3, arg4]}
    (arg6 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalModelEndpointSupportData.jsonData 3344
        [arg0, arg1, arg2, arg3, arg4, arg5])
    (arg7 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalModelEndpointSupportData.jsonData 3344
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6])
    (arg8 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalModelEndpointSupportData.jsonData 3344
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7])
    :
    recovered_closed_result_type%
      DaggerRecoveredGlobalModelEndpointSupportData.jsonData 3344
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredGlobalModelEndpointSupportData.jsonData 3344 :=
    @(recovered_closed_expr%
      DaggerRecoveredGlobalModelEndpointSupportData.jsonData 3353)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5 arg6 arg7 arg8

theorem DaggerGlobalDKClosure.source_retract.{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalModelEndpointSupportData.jsonData 2398 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalModelEndpointSupportData.jsonData 2574)

noncomputable def DaggerGlobalDKClosure.inclusionEndpoint.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalModelEndpointSupportData.jsonData 3876
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalModelEndpointSupportData.jsonData 3876
        [arg0]}
    {arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalModelEndpointSupportData.jsonData 3876
        [arg0, arg1]}
    {arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalModelEndpointSupportData.jsonData 3876
        [arg0, arg1, arg2]}
    {arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalModelEndpointSupportData.jsonData 3876
        [arg0, arg1, arg2, arg3]}
    {arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalModelEndpointSupportData.jsonData 3876
        [arg0, arg1, arg2, arg3, arg4]}
    (arg6 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalModelEndpointSupportData.jsonData 3876
        [arg0, arg1, arg2, arg3, arg4, arg5])
    (arg7 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalModelEndpointSupportData.jsonData 3876
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6])
    :
    recovered_closed_result_type%
      DaggerRecoveredGlobalModelEndpointSupportData.jsonData 3876
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredGlobalModelEndpointSupportData.jsonData 3876 :=
    @(recovered_closed_expr%
      DaggerRecoveredGlobalModelEndpointSupportData.jsonData 3916)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5 arg6 arg7

theorem DaggerGlobalDKClosure.inclusionTarget._proof_1.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredGlobalModelEndpointSupportData.jsonData 3507 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalModelEndpointSupportData.jsonData 3529)

noncomputable def DaggerGlobalDKClosure.inclusionTarget.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalModelEndpointSupportData.jsonData 5160
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalModelEndpointSupportData.jsonData 5160
        [arg0]}
    {arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalModelEndpointSupportData.jsonData 5160
        [arg0, arg1]}
    {arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalModelEndpointSupportData.jsonData 5160
        [arg0, arg1, arg2]}
    {arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalModelEndpointSupportData.jsonData 5160
        [arg0, arg1, arg2, arg3]}
    {arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalModelEndpointSupportData.jsonData 5160
        [arg0, arg1, arg2, arg3, arg4]}
    (arg6 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalModelEndpointSupportData.jsonData 5160
        [arg0, arg1, arg2, arg3, arg4, arg5])
    (arg7 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalModelEndpointSupportData.jsonData 5160
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6])
    (arg8 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalModelEndpointSupportData.jsonData 5160
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7])
    :
    recovered_closed_result_type%
      DaggerRecoveredGlobalModelEndpointSupportData.jsonData 5160
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredGlobalModelEndpointSupportData.jsonData 5160 :=
    @(recovered_closed_expr%
      DaggerRecoveredGlobalModelEndpointSupportData.jsonData 5169)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5 arg6 arg7 arg8

theorem DaggerGlobalDKClosure.inclusion_square.{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalModelEndpointSupportData.jsonData 5237 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalModelEndpointSupportData.jsonData 5717)

noncomputable def DaggerGlobalDKClosure.retractionEndpoint.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalModelEndpointSupportData.jsonData 3794
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalModelEndpointSupportData.jsonData 3794
        [arg0]}
    {arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalModelEndpointSupportData.jsonData 3794
        [arg0, arg1]}
    {arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalModelEndpointSupportData.jsonData 3794
        [arg0, arg1, arg2]}
    {arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalModelEndpointSupportData.jsonData 3794
        [arg0, arg1, arg2, arg3]}
    {arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalModelEndpointSupportData.jsonData 3794
        [arg0, arg1, arg2, arg3, arg4]}
    (arg6 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalModelEndpointSupportData.jsonData 3794
        [arg0, arg1, arg2, arg3, arg4, arg5])
    (arg7 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalModelEndpointSupportData.jsonData 3794
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6])
    :
    recovered_closed_result_type%
      DaggerRecoveredGlobalModelEndpointSupportData.jsonData 3794
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredGlobalModelEndpointSupportData.jsonData 3794 :=
    @(recovered_closed_expr%
      DaggerRecoveredGlobalModelEndpointSupportData.jsonData 3831)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5 arg6 arg7

noncomputable def DaggerGlobalDKClosure.retractionTarget.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalModelEndpointSupportData.jsonData 3668
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalModelEndpointSupportData.jsonData 3668
        [arg0]}
    {arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalModelEndpointSupportData.jsonData 3668
        [arg0, arg1]}
    {arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalModelEndpointSupportData.jsonData 3668
        [arg0, arg1, arg2]}
    {arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalModelEndpointSupportData.jsonData 3668
        [arg0, arg1, arg2, arg3]}
    {arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalModelEndpointSupportData.jsonData 3668
        [arg0, arg1, arg2, arg3, arg4]}
    (arg6 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalModelEndpointSupportData.jsonData 3668
        [arg0, arg1, arg2, arg3, arg4, arg5])
    (arg7 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalModelEndpointSupportData.jsonData 3668
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6])
    (arg8 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalModelEndpointSupportData.jsonData 3668
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7])
    :
    recovered_closed_result_type%
      DaggerRecoveredGlobalModelEndpointSupportData.jsonData 3668
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredGlobalModelEndpointSupportData.jsonData 3668 :=
    @(recovered_closed_expr%
      DaggerRecoveredGlobalModelEndpointSupportData.jsonData 3722)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5 arg6 arg7 arg8

theorem DaggerGlobalDKClosure.retraction_square.{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalModelEndpointSupportData.jsonData 5738 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalModelEndpointSupportData.jsonData 6354)

noncomputable def DaggerGlobalDKClosure.targetSplit.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalModelEndpointSupportData.jsonData 5181
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalModelEndpointSupportData.jsonData 5181
        [arg0]}
    {arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalModelEndpointSupportData.jsonData 5181
        [arg0, arg1]}
    {arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalModelEndpointSupportData.jsonData 5181
        [arg0, arg1, arg2]}
    {arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalModelEndpointSupportData.jsonData 5181
        [arg0, arg1, arg2, arg3]}
    {arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalModelEndpointSupportData.jsonData 5181
        [arg0, arg1, arg2, arg3, arg4]}
    (arg6 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalModelEndpointSupportData.jsonData 5181
        [arg0, arg1, arg2, arg3, arg4, arg5])
    (arg7 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalModelEndpointSupportData.jsonData 5181
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6])
    :
    recovered_closed_result_type%
      DaggerRecoveredGlobalModelEndpointSupportData.jsonData 5181
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredGlobalModelEndpointSupportData.jsonData 5181 :=
    @(recovered_closed_expr%
      DaggerRecoveredGlobalModelEndpointSupportData.jsonData 5216)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5 arg6 arg7

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerGlobalDKClosure.inclusionTarget.eq_1)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerGlobalDKClosure.retractionTarget.eq_1)
  pure ()

theorem DaggerGlobalDKClosure.target_retract.{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalModelEndpointSupportData.jsonData 3934 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalModelEndpointSupportData.jsonData 4760)

theorem DaggerGlobalDKClosure.homRetract._proof_1.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredGlobalModelEndpointSupportData.jsonData 5113 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalModelEndpointSupportData.jsonData 5151)

noncomputable def DaggerGlobalDKClosure.homRetract.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalModelEndpointSupportData.jsonData 3143
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalModelEndpointSupportData.jsonData 3143
        [arg0]}
    {arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalModelEndpointSupportData.jsonData 3143
        [arg0, arg1]}
    {arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalModelEndpointSupportData.jsonData 3143
        [arg0, arg1, arg2]}
    {arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalModelEndpointSupportData.jsonData 3143
        [arg0, arg1, arg2, arg3]}
    {arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalModelEndpointSupportData.jsonData 3143
        [arg0, arg1, arg2, arg3, arg4]}
    (arg6 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalModelEndpointSupportData.jsonData 3143
        [arg0, arg1, arg2, arg3, arg4, arg5])
    (arg7 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalModelEndpointSupportData.jsonData 3143
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6])
    (arg8 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalModelEndpointSupportData.jsonData 3143
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7])
    :
    recovered_closed_result_type%
      DaggerRecoveredGlobalModelEndpointSupportData.jsonData 3143
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredGlobalModelEndpointSupportData.jsonData 3143 :=
    @(recovered_closed_expr%
      DaggerRecoveredGlobalModelEndpointSupportData.jsonData 3235)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5 arg6 arg7 arg8

noncomputable def DaggerGlobalDKClosure.witnessSource.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalModelEndpointSupportData.jsonData 3278
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalModelEndpointSupportData.jsonData 3278
        [arg0]}
    {arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalModelEndpointSupportData.jsonData 3278
        [arg0, arg1]}
    {arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalModelEndpointSupportData.jsonData 3278
        [arg0, arg1, arg2]}
    {arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalModelEndpointSupportData.jsonData 3278
        [arg0, arg1, arg2, arg3]}
    {arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalModelEndpointSupportData.jsonData 3278
        [arg0, arg1, arg2, arg3, arg4]}
    (arg6 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalModelEndpointSupportData.jsonData 3278
        [arg0, arg1, arg2, arg3, arg4, arg5])
    (arg7 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalModelEndpointSupportData.jsonData 3278
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6])
    :
    recovered_closed_result_type%
      DaggerRecoveredGlobalModelEndpointSupportData.jsonData 3278
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredGlobalModelEndpointSupportData.jsonData 3278 :=
    @(recovered_closed_expr%
      DaggerRecoveredGlobalModelEndpointSupportData.jsonData 3334)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5 arg6 arg7

noncomputable def DaggerGlobalDKClosure.retractedClass.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalModelEndpointSupportData.jsonData 3585
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalModelEndpointSupportData.jsonData 3585
        [arg0]}
    {arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalModelEndpointSupportData.jsonData 3585
        [arg0, arg1]}
    {arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalModelEndpointSupportData.jsonData 3585
        [arg0, arg1, arg2]}
    {arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalModelEndpointSupportData.jsonData 3585
        [arg0, arg1, arg2, arg3]}
    {arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalModelEndpointSupportData.jsonData 3585
        [arg0, arg1, arg2, arg3, arg4]}
    (arg6 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalModelEndpointSupportData.jsonData 3585
        [arg0, arg1, arg2, arg3, arg4, arg5])
    (arg7 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalModelEndpointSupportData.jsonData 3585
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6])
    (arg8 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalModelEndpointSupportData.jsonData 3585
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7])
    (arg9 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalModelEndpointSupportData.jsonData 3585
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8])
    :
    recovered_closed_result_type%
      DaggerRecoveredGlobalModelEndpointSupportData.jsonData 3585
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredGlobalModelEndpointSupportData.jsonData 3585 :=
    @(recovered_closed_expr%
      DaggerRecoveredGlobalModelEndpointSupportData.jsonData 3657)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5 arg6 arg7 arg8 arg9

theorem DaggerGlobalDKClosure.retractedClass_coherentlyUnitary.{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalModelEndpointSupportData.jsonData 4818 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalModelEndpointSupportData.jsonData 4916)

theorem DaggerGlobalDKClosure.daggerDK_of_retract.{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalModelEndpointSupportData.jsonData 2592 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalModelEndpointSupportData.jsonData 3092)

