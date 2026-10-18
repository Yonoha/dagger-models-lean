import OriginalCofibrationSOARecovered
import OriginalDKHomRetractsRecovered
import OriginalRecoveredClosedExpressionApplication
import OriginalRecoveredGlobalLeftProperData

/-! Original CofibrationHomRetract, with unchanged closed types and values. -/

set_option autoImplicit false
set_option maxRecDepth 100000

theorem DaggerCofibrationPushoutRetract.instHasPushoutsG_cofibrationHomRetract.{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 188439 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 191293)

noncomputable def DaggerCofibrationPushoutRetract.originalRetract.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 192734
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 192734
        [arg0]}
    {arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 192734
        [arg0, arg1]}
    {arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 192734
        [arg0, arg1, arg2]}
    {arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 192734
        [arg0, arg1, arg2, arg3]}
    {arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 192734
        [arg0, arg1, arg2, arg3, arg4]}
    {arg6 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 192734
        [arg0, arg1, arg2, arg3, arg4, arg5]}
    {arg7 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 192734
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6]}
    {arg8 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 192734
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7]}
    (arg9 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 192734
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8])
    (arg10 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 192734
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9])
    {arg11 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 192734
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10]}
    {arg12 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 192734
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11]}
    (arg13 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 192734
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11, arg12])
    :
    recovered_closed_result_type%
      DaggerRecoveredGlobalLeftProperData.jsonData 192734
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11, arg12, arg13]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 192734 :=
    @(recovered_closed_expr%
      DaggerRecoveredGlobalLeftProperData.jsonData 192792)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5 arg6 arg7 arg8 arg9 arg10 arg11 arg12 arg13

noncomputable def DaggerCofibrationPushoutRetract.originalHomRetract.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 192814
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 192814
        [arg0]}
    {arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 192814
        [arg0, arg1]}
    {arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 192814
        [arg0, arg1, arg2]}
    {arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 192814
        [arg0, arg1, arg2, arg3]}
    {arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 192814
        [arg0, arg1, arg2, arg3, arg4]}
    {arg6 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 192814
        [arg0, arg1, arg2, arg3, arg4, arg5]}
    {arg7 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 192814
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6]}
    {arg8 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 192814
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7]}
    (arg9 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 192814
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8])
    (arg10 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 192814
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9])
    {arg11 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 192814
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10]}
    {arg12 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 192814
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11]}
    (arg13 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 192814
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11, arg12])
    (arg14 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 192814
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11, arg12, arg13])
    (arg15 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 192814
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11, arg12, arg13,
         arg14])
    :
    recovered_closed_result_type%
      DaggerRecoveredGlobalLeftProperData.jsonData 192814
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11, arg12, arg13,
       arg14, arg15]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 192814 :=
    @(recovered_closed_expr%
      DaggerRecoveredGlobalLeftProperData.jsonData 192854)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5 arg6 arg7 arg8 arg9 arg10 arg11 arg12 arg13 arg14 arg15

theorem DaggerCofibrationPushoutRetract.original_inclusion_endpoint.{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 191859 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 191898)

theorem DaggerCofibrationPushoutRetract.originalHomRetract_i_right.{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 191517 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 191535)

theorem DaggerCofibrationPushoutRetract.originalHomRetract_target_split.{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 191569 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 191594)

theorem DaggerCofibrationPushoutRetract.canonicalObj._proof_1.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 192108 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 192120)

noncomputable def DaggerCofibrationPushoutRetract.canonicalObj.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 192909
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 192909
        [arg0]}
    {arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 192909
        [arg0, arg1]}
    {arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 192909
        [arg0, arg1, arg2]}
    {arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 192909
        [arg0, arg1, arg2, arg3]}
    :
    recovered_closed_result_type%
      DaggerRecoveredGlobalLeftProperData.jsonData 192909
      [arg0, arg1, arg2, arg3, arg4]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 192909 :=
    @(recovered_closed_expr%
      DaggerRecoveredGlobalLeftProperData.jsonData 192922)
  exact @f arg0 arg1 arg2 arg3 arg4

noncomputable def DaggerCofibrationPushoutRetract.canonicalComparison.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 192634
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 192634
        [arg0]}
    {arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 192634
        [arg0, arg1]}
    {arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 192634
        [arg0, arg1, arg2]}
    {arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 192634
        [arg0, arg1, arg2, arg3]}
    :
    recovered_closed_result_type%
      DaggerRecoveredGlobalLeftProperData.jsonData 192634
      [arg0, arg1, arg2, arg3, arg4]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 192634 :=
    @(recovered_closed_expr%
      DaggerRecoveredGlobalLeftProperData.jsonData 192647)
  exact @f arg0 arg1 arg2 arg3 arg4

noncomputable def DaggerCofibrationPushoutRetract.canonicalLeft.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 192701
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 192701
        [arg0]}
    {arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 192701
        [arg0, arg1]}
    {arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 192701
        [arg0, arg1, arg2]}
    {arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 192701
        [arg0, arg1, arg2, arg3]}
    :
    recovered_closed_result_type%
      DaggerRecoveredGlobalLeftProperData.jsonData 192701
      [arg0, arg1, arg2, arg3, arg4]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 192701 :=
    @(recovered_closed_expr%
      DaggerRecoveredGlobalLeftProperData.jsonData 192714)
  exact @f arg0 arg1 arg2 arg3 arg4

theorem DaggerCofibrationPushoutRetract.canonicalSquare.{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 192153 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 192172)

noncomputable def DaggerCofibrationPushoutRetract.canonicalHomRetract.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 191680
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 191680
        [arg0]}
    {arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 191680
        [arg0, arg1]}
    {arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 191680
        [arg0, arg1, arg2]}
    {arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 191680
        [arg0, arg1, arg2, arg3]}
    {arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 191680
        [arg0, arg1, arg2, arg3, arg4]}
    {arg6 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 191680
        [arg0, arg1, arg2, arg3, arg4, arg5]}
    {arg7 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 191680
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6]}
    (arg8 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 191680
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7])
    (arg9 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 191680
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8])
    (arg10 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 191680
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9])
    (arg11 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 191680
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10])
    :
    recovered_closed_result_type%
      DaggerRecoveredGlobalLeftProperData.jsonData 191680
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 191680 :=
    @(recovered_closed_expr%
      DaggerRecoveredGlobalLeftProperData.jsonData 191720)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5 arg6 arg7 arg8 arg9 arg10 arg11

theorem DaggerCofibrationPushoutRetract.originalHomRetract_inclusion_square.{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 191763 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 191788)

noncomputable abbrev DaggerCofibrationPushoutRetract.Geometric.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 39828
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 39828
        [arg0]}
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 39828
        [arg0, arg1])
    :
    recovered_closed_result_type%
      DaggerRecoveredGlobalLeftProperData.jsonData 39828
      [arg0, arg1, arg2]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 39828 :=
    @(recovered_closed_expr%
      DaggerRecoveredGlobalLeftProperData.jsonData 39831)
  exact @f arg0 arg1 arg2

theorem DaggerCofibrationPushoutRetract.original_local_geometric.{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 191949 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 192082)

theorem DaggerCofibrationPushoutRetract.canonical_local_geometric.{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 192216 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 192263)

theorem DaggerCofibrationPushoutRetract.originalHomRetract_i_left.{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 192288 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 192306)

theorem DaggerCofibrationPushoutRetract.original_retraction_endpoint.{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 192518 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 192542)

theorem DaggerCofibrationPushoutRetract.originalHomRetract_r_right.{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 192396 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 192414)

noncomputable def DaggerCofibrationPushoutRetract.canonicalRetract.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 192440
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 192440
        [arg0]}
    {arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 192440
        [arg0, arg1]}
    {arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 192440
        [arg0, arg1, arg2]}
    {arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 192440
        [arg0, arg1, arg2, arg3]}
    {arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 192440
        [arg0, arg1, arg2, arg3, arg4]}
    {arg6 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 192440
        [arg0, arg1, arg2, arg3, arg4, arg5]}
    {arg7 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 192440
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6]}
    (arg8 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 192440
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7])
    (arg9 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 192440
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8])
    :
    recovered_closed_result_type%
      DaggerRecoveredGlobalLeftProperData.jsonData 192440
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 192440 :=
    @(recovered_closed_expr%
      DaggerRecoveredGlobalLeftProperData.jsonData 192474)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5 arg6 arg7 arg8 arg9

theorem DaggerCofibrationPushoutRetract.original_source_split.{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 192671 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 192695)

theorem DaggerCofibrationPushoutRetract.originalHomRetract_r_left.{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 192609 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 192627)

theorem DaggerCofibrationPushoutRetract.originalHomRetract_source_split.{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 192878 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 192904)

theorem DaggerCofibrationPushoutRetract.originalHomRetract_retraction_square.{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 192951 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 192977)

