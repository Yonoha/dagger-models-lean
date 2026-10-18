import OriginalSmithSolutionsRecovered
import OriginalRecoveredClosedExpressionApplication
import OriginalRecoveredSmithModelConstructionData

/-! Original SmithPushouts, with unchanged closed types and values. -/

set_option autoImplicit false
set_option maxRecDepth 100000

theorem DaggerSmithSolutionSet.instHasColimitsOfSize_smithPushouts.{w, v, u} :
  recovered_closed_expr%
    DaggerRecoveredSmithModelConstructionData.jsonData 12477 :=
  @(recovered_closed_expr%
    DaggerRecoveredSmithModelConstructionData.jsonData 12484)

theorem DaggerSmithSolutionSet.suppliedPushoutIso._proof_1.{u_1, u_2, u_3} :
  recovered_closed_expr%
    DaggerRecoveredSmithModelConstructionData.jsonData 15098 :=
  @(recovered_closed_expr%
    DaggerRecoveredSmithModelConstructionData.jsonData 15126)

noncomputable def DaggerSmithSolutionSet.suppliedPushoutIso.{w, v, u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredSmithModelConstructionData.jsonData 14826
        []}
    [arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredSmithModelConstructionData.jsonData 14826
        [arg0]]
    [arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredSmithModelConstructionData.jsonData 14826
        [arg0, arg1]]
    {arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredSmithModelConstructionData.jsonData 14826
        [arg0, arg1, arg2]}
    {arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredSmithModelConstructionData.jsonData 14826
        [arg0, arg1, arg2, arg3]}
    (arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredSmithModelConstructionData.jsonData 14826
        [arg0, arg1, arg2, arg3, arg4])
    (arg6 :
      recovered_closed_binder_type%
        DaggerRecoveredSmithModelConstructionData.jsonData 14826
        [arg0, arg1, arg2, arg3, arg4, arg5])
    (arg7 :
      recovered_closed_binder_type%
        DaggerRecoveredSmithModelConstructionData.jsonData 14826
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6])
    (arg8 :
      recovered_closed_binder_type%
        DaggerRecoveredSmithModelConstructionData.jsonData 14826
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7])
    {arg9 :
      recovered_closed_binder_type%
        DaggerRecoveredSmithModelConstructionData.jsonData 14826
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8]}
    {arg10 :
      recovered_closed_binder_type%
        DaggerRecoveredSmithModelConstructionData.jsonData 14826
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9]}
    {arg11 :
      recovered_closed_binder_type%
        DaggerRecoveredSmithModelConstructionData.jsonData 14826
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10]}
    (arg12 :
      recovered_closed_binder_type%
        DaggerRecoveredSmithModelConstructionData.jsonData 14826
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11])
    :
    recovered_closed_result_type%
      DaggerRecoveredSmithModelConstructionData.jsonData 14826
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11, arg12]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredSmithModelConstructionData.jsonData 14826 :=
    @(recovered_closed_expr%
      DaggerRecoveredSmithModelConstructionData.jsonData 14862)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5 arg6 arg7 arg8 arg9 arg10 arg11 arg12

theorem DaggerSmithSolutionSet.supplied_inl_inv.{w, v, u} :
  recovered_closed_expr%
    DaggerRecoveredSmithModelConstructionData.jsonData 14739 :=
  @(recovered_closed_expr%
    DaggerRecoveredSmithModelConstructionData.jsonData 14765)

theorem DaggerSmithSolutionSet.supplied_inl_inv_assoc.{w, v, u} :
  recovered_closed_expr%
    DaggerRecoveredSmithModelConstructionData.jsonData 13487 :=
  @(recovered_closed_expr%
    DaggerRecoveredSmithModelConstructionData.jsonData 13719)

theorem DaggerSmithSolutionSet.supplied_inr.{w, v, u} :
  recovered_closed_expr%
    DaggerRecoveredSmithModelConstructionData.jsonData 13757 :=
  @(recovered_closed_expr%
    DaggerRecoveredSmithModelConstructionData.jsonData 13783)

theorem DaggerSmithSolutionSet.supplied_inr_assoc.{w, v, u} :
  recovered_closed_expr%
    DaggerRecoveredSmithModelConstructionData.jsonData 13923 :=
  @(recovered_closed_expr%
    DaggerRecoveredSmithModelConstructionData.jsonData 14082)

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerSmithSolutionSet.suppliedPushoutIso.congr_simp)
  pure ()

theorem DaggerSmithSolutionSet.supplied_inr_inv.{w, v, u} :
  recovered_closed_expr%
    DaggerRecoveredSmithModelConstructionData.jsonData 14783 :=
  @(recovered_closed_expr%
    DaggerRecoveredSmithModelConstructionData.jsonData 14809)

theorem DaggerSmithSolutionSet.supplied_inr_inv_assoc.{w, v, u} :
  recovered_closed_expr%
    DaggerRecoveredSmithModelConstructionData.jsonData 14499 :=
  @(recovered_closed_expr%
    DaggerRecoveredSmithModelConstructionData.jsonData 14579)

noncomputable def DaggerSmithSolutionSet.generatorPushout.{w, v, u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredSmithModelConstructionData.jsonData 14705
        []}
    [arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredSmithModelConstructionData.jsonData 14705
        [arg0]]
    [arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredSmithModelConstructionData.jsonData 14705
        [arg0, arg1]]
    {arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredSmithModelConstructionData.jsonData 14705
        [arg0, arg1, arg2]}
    {arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredSmithModelConstructionData.jsonData 14705
        [arg0, arg1, arg2, arg3]}
    (arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredSmithModelConstructionData.jsonData 14705
        [arg0, arg1, arg2, arg3, arg4])
    (arg6 :
      recovered_closed_binder_type%
        DaggerRecoveredSmithModelConstructionData.jsonData 14705
        [arg0, arg1, arg2, arg3, arg4, arg5])
    (arg7 :
      recovered_closed_binder_type%
        DaggerRecoveredSmithModelConstructionData.jsonData 14705
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6])
    (arg8 :
      recovered_closed_binder_type%
        DaggerRecoveredSmithModelConstructionData.jsonData 14705
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7])
    :
    recovered_closed_result_type%
      DaggerRecoveredSmithModelConstructionData.jsonData 14705
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredSmithModelConstructionData.jsonData 14705 :=
    @(recovered_closed_expr%
      DaggerRecoveredSmithModelConstructionData.jsonData 14723)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5 arg6 arg7 arg8

theorem DaggerSmithSolutionSet.supplied_inl.{w, v, u} :
  recovered_closed_expr%
    DaggerRecoveredSmithModelConstructionData.jsonData 14984 :=
  @(recovered_closed_expr%
    DaggerRecoveredSmithModelConstructionData.jsonData 15010)

theorem DaggerSmithSolutionSet.supplied_inl_assoc.{w, v, u} :
  recovered_closed_expr%
    DaggerRecoveredSmithModelConstructionData.jsonData 14881 :=
  @(recovered_closed_expr%
    DaggerRecoveredSmithModelConstructionData.jsonData 14967)

