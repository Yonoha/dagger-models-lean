import OriginalSmithSolutionsRecovered
import OriginalRecoveredClosedExpressionApplication
import OriginalRecoveredSmithModelConstructionData

/-! Original SmithDensity, with unchanged closed types and values. -/

set_option autoImplicit false
set_option maxRecDepth 100000

structure DaggerSmithSolutionSet.SolutionFactor.{w, v, u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredSmithModelConstructionData.jsonData 733
        []}
    [arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredSmithModelConstructionData.jsonData 733
        [arg0]]
    {arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredSmithModelConstructionData.jsonData 733
        [arg0, arg1]}
    {arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredSmithModelConstructionData.jsonData 733
        [arg0, arg1, arg2]}
    (arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredSmithModelConstructionData.jsonData 733
        [arg0, arg1, arg2, arg3])
    (arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredSmithModelConstructionData.jsonData 733
        [arg0, arg1, arg2, arg3, arg4])
    (arg6 :
      recovered_closed_binder_type%
        DaggerRecoveredSmithModelConstructionData.jsonData 733
        [arg0, arg1, arg2, arg3, arg4, arg5])
    (arg7 :
      recovered_closed_binder_type%
        DaggerRecoveredSmithModelConstructionData.jsonData 733
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6])
    :
      recovered_closed_result_type%
        DaggerRecoveredSmithModelConstructionData.jsonData 733
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7] where
  s :
    recovered_closed_binder_type%
      DaggerRecoveredSmithModelConstructionData.jsonData 205
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7]
  α :
    recovered_closed_binder_type%
      DaggerRecoveredSmithModelConstructionData.jsonData 205
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, s]
  β :
    recovered_closed_binder_type%
      DaggerRecoveredSmithModelConstructionData.jsonData 205
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, s, α]
  fac :
    recovered_closed_binder_type%
      DaggerRecoveredSmithModelConstructionData.jsonData 205
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, s, α, β]

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerSmithSolutionSet.SolutionFactor)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerSmithSolutionSet.SolutionFactor._sizeOf_1)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerSmithSolutionSet.SolutionFactor._sizeOf_inst)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerSmithSolutionSet.SolutionFactor.casesOn)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerSmithSolutionSet.SolutionFactor.ctorIdx)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerSmithSolutionSet.SolutionFactor.fac)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerSmithSolutionSet.SolutionFactor.mk)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerSmithSolutionSet.SolutionFactor.mk._flat_ctor)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerSmithSolutionSet.SolutionFactor.mk.inj)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerSmithSolutionSet.SolutionFactor.mk.injEq)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerSmithSolutionSet.SolutionFactor.mk.noConfusion)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerSmithSolutionSet.SolutionFactor.mk.sizeOf_spec)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerSmithSolutionSet.SolutionFactor.noConfusion)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerSmithSolutionSet.SolutionFactor.noConfusionType)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerSmithSolutionSet.SolutionFactor.rec)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerSmithSolutionSet.SolutionFactor.recOn)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerSmithSolutionSet.SolutionFactor.s)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerSmithSolutionSet.SolutionFactor.α)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerSmithSolutionSet.SolutionFactor.β)
  pure ()

theorem DaggerSmithSolutionSet.solutionFactor._proof_1.{u_1, u_2, u_3} :
  recovered_closed_expr%
    DaggerRecoveredSmithModelConstructionData.jsonData 8641 :=
  @(recovered_closed_expr%
    DaggerRecoveredSmithModelConstructionData.jsonData 8969)

noncomputable def DaggerSmithSolutionSet.solutionFactor.{w, v, u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredSmithModelConstructionData.jsonData 6605
        []}
    [arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredSmithModelConstructionData.jsonData 6605
        [arg0]]
    {arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredSmithModelConstructionData.jsonData 6605
        [arg0, arg1]}
    {arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredSmithModelConstructionData.jsonData 6605
        [arg0, arg1, arg2]}
    (arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredSmithModelConstructionData.jsonData 6605
        [arg0, arg1, arg2, arg3])
    (arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredSmithModelConstructionData.jsonData 6605
        [arg0, arg1, arg2, arg3, arg4])
    (arg6 :
      recovered_closed_binder_type%
        DaggerRecoveredSmithModelConstructionData.jsonData 6605
        [arg0, arg1, arg2, arg3, arg4, arg5])
    (arg7 :
      recovered_closed_binder_type%
        DaggerRecoveredSmithModelConstructionData.jsonData 6605
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6])
    (arg8 :
      recovered_closed_binder_type%
        DaggerRecoveredSmithModelConstructionData.jsonData 6605
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7])
    :
    recovered_closed_result_type%
      DaggerRecoveredSmithModelConstructionData.jsonData 6605
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredSmithModelConstructionData.jsonData 6605 :=
    @(recovered_closed_expr%
      DaggerRecoveredSmithModelConstructionData.jsonData 6627)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5 arg6 arg7 arg8

theorem DaggerSmithSolutionSet.densityLift._proof_1.{u_1, u_2, u_3} :
  recovered_closed_expr%
    DaggerRecoveredSmithModelConstructionData.jsonData 10771 :=
  @(recovered_closed_expr%
    DaggerRecoveredSmithModelConstructionData.jsonData 10804)

theorem DaggerSmithSolutionSet.densityLift._proof_2.{u_1, u_2, u_3} :
  recovered_closed_expr%
    DaggerRecoveredSmithModelConstructionData.jsonData 1090 :=
  @(recovered_closed_expr%
    DaggerRecoveredSmithModelConstructionData.jsonData 1365)

theorem DaggerSmithSolutionSet.densityLift._proof_3.{u_1, u_2, u_3} :
  recovered_closed_expr%
    DaggerRecoveredSmithModelConstructionData.jsonData 1409 :=
  @(recovered_closed_expr%
    DaggerRecoveredSmithModelConstructionData.jsonData 1456)

theorem DaggerSmithSolutionSet.densityLift._proof_6.{u_1, u_2, u_3} :
  recovered_closed_expr%
    DaggerRecoveredSmithModelConstructionData.jsonData 6106 :=
  @(recovered_closed_expr%
    DaggerRecoveredSmithModelConstructionData.jsonData 6190)

theorem DaggerSmithSolutionSet.densityLift._proof_4.{u_1, u_2, u_3} :
  recovered_closed_expr%
    DaggerRecoveredSmithModelConstructionData.jsonData 10863 :=
  @(recovered_closed_expr%
    DaggerRecoveredSmithModelConstructionData.jsonData 10882)

theorem DaggerSmithSolutionSet.densityLift._proof_5.{u_1, u_2} :
  recovered_closed_expr%
    DaggerRecoveredSmithModelConstructionData.jsonData 10539 :=
  @(recovered_closed_expr%
    DaggerRecoveredSmithModelConstructionData.jsonData 10554)

theorem DaggerSmithSolutionSet.densityLift._proof_7.{u_1, u_2, u_3} :
  recovered_closed_expr%
    DaggerRecoveredSmithModelConstructionData.jsonData 7706 :=
  @(recovered_closed_expr%
    DaggerRecoveredSmithModelConstructionData.jsonData 8313)

theorem DaggerSmithSolutionSet.densityLift._proof_8.{u_1, u_2, u_3} :
  recovered_closed_expr%
    DaggerRecoveredSmithModelConstructionData.jsonData 7010 :=
  @(recovered_closed_expr%
    DaggerRecoveredSmithModelConstructionData.jsonData 7527)

noncomputable def DaggerSmithSolutionSet.densityLift.{w, v, u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredSmithModelConstructionData.jsonData 9043
        []}
    [arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredSmithModelConstructionData.jsonData 9043
        [arg0]]
    [arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredSmithModelConstructionData.jsonData 9043
        [arg0, arg1]]
    {arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredSmithModelConstructionData.jsonData 9043
        [arg0, arg1, arg2]}
    {arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredSmithModelConstructionData.jsonData 9043
        [arg0, arg1, arg2, arg3]}
    [arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredSmithModelConstructionData.jsonData 9043
        [arg0, arg1, arg2, arg3, arg4]]
    (arg6 :
      recovered_closed_binder_type%
        DaggerRecoveredSmithModelConstructionData.jsonData 9043
        [arg0, arg1, arg2, arg3, arg4, arg5])
    {arg7 :
      recovered_closed_binder_type%
        DaggerRecoveredSmithModelConstructionData.jsonData 9043
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6]}
    {arg8 :
      recovered_closed_binder_type%
        DaggerRecoveredSmithModelConstructionData.jsonData 9043
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7]}
    {arg9 :
      recovered_closed_binder_type%
        DaggerRecoveredSmithModelConstructionData.jsonData 9043
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8]}
    {arg10 :
      recovered_closed_binder_type%
        DaggerRecoveredSmithModelConstructionData.jsonData 9043
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9]}
    (arg11 :
      recovered_closed_binder_type%
        DaggerRecoveredSmithModelConstructionData.jsonData 9043
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10])
    (arg12 :
      recovered_closed_binder_type%
        DaggerRecoveredSmithModelConstructionData.jsonData 9043
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11])
    (arg13 :
      recovered_closed_binder_type%
        DaggerRecoveredSmithModelConstructionData.jsonData 9043
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11, arg12])
    (arg14 :
      recovered_closed_binder_type%
        DaggerRecoveredSmithModelConstructionData.jsonData 9043
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11, arg12, arg13])
    (arg15 :
      recovered_closed_binder_type%
        DaggerRecoveredSmithModelConstructionData.jsonData 9043
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11, arg12, arg13,
         arg14])
    (arg16 :
      recovered_closed_binder_type%
        DaggerRecoveredSmithModelConstructionData.jsonData 9043
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11, arg12, arg13,
         arg14, arg15])
    :
    recovered_closed_result_type%
      DaggerRecoveredSmithModelConstructionData.jsonData 9043
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11, arg12, arg13,
       arg14, arg15, arg16]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredSmithModelConstructionData.jsonData 9043 :=
    @(recovered_closed_expr%
      DaggerRecoveredSmithModelConstructionData.jsonData 10377)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5 arg6 arg7 arg8 arg9 arg10 arg11 arg12 arg13 arg14 arg15
    arg16

theorem DaggerSmithSolutionSet.density.{w, v, u} :
  recovered_closed_expr%
    DaggerRecoveredSmithModelConstructionData.jsonData 6352 :=
  @(recovered_closed_expr%
    DaggerRecoveredSmithModelConstructionData.jsonData 6527)

