import OriginalFiniteRelativeExtensionSupportRecovered
import OriginalRecoveredClosedExpressionApplication
import OriginalRecoveredFiniteRelativeExtensionData

/-! Original FiniteRelativeExtensionCompact, with unchanged closed types and values. -/

set_option autoImplicit false
set_option maxRecDepth 100000

structure DaggerFiniteRelativeExtension.SupportedNullhomotopy.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 6493
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 6493
        [arg0]}
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 6493
        [arg0, arg1])
    {arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 6493
        [arg0, arg1, arg2]}
    (arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 6493
        [arg0, arg1, arg2, arg3])
    (arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 6493
        [arg0, arg1, arg2, arg3, arg4])
    (arg6 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 6493
        [arg0, arg1, arg2, arg3, arg4, arg5])
    :
      recovered_closed_result_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 6493
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6] where
  F :
    recovered_closed_binder_type%
      DaggerRecoveredFiniteRelativeExtensionData.jsonData 6674
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6]
  finiteF :
    recovered_closed_binder_type%
      DaggerRecoveredFiniteRelativeExtensionData.jsonData 6674
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, F]
  point :
    recovered_closed_binder_type%
      DaggerRecoveredFiniteRelativeExtensionData.jsonData 6674
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, F, finiteF]
  point_over :
    recovered_closed_binder_type%
      DaggerRecoveredFiniteRelativeExtensionData.jsonData 6674
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, F, finiteF, point]
  homotopy :
    recovered_closed_binder_type%
      DaggerRecoveredFiniteRelativeExtensionData.jsonData 6674
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, F, finiteF, point, point_over]
  homotopy_over :
    recovered_closed_binder_type%
      DaggerRecoveredFiniteRelativeExtensionData.jsonData 6674
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, F, finiteF, point, point_over, homotopy]

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteRelativeExtension.SupportedNullhomotopy)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteRelativeExtension.SupportedNullhomotopy.F)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteRelativeExtension.SupportedNullhomotopy._sizeOf_1)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteRelativeExtension.SupportedNullhomotopy._sizeOf_inst)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteRelativeExtension.SupportedNullhomotopy.casesOn)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteRelativeExtension.SupportedNullhomotopy.ctorIdx)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteRelativeExtension.SupportedNullhomotopy.finiteF)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteRelativeExtension.SupportedNullhomotopy.homotopy)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteRelativeExtension.SupportedNullhomotopy.homotopy_over)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteRelativeExtension.SupportedNullhomotopy.mk)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteRelativeExtension.SupportedNullhomotopy.mk._flat_ctor)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteRelativeExtension.SupportedNullhomotopy.mk.inj)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteRelativeExtension.SupportedNullhomotopy.mk.injEq)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteRelativeExtension.SupportedNullhomotopy.mk.noConfusion)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteRelativeExtension.SupportedNullhomotopy.mk.sizeOf_spec)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteRelativeExtension.SupportedNullhomotopy.noConfusion)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteRelativeExtension.SupportedNullhomotopy.noConfusionType)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteRelativeExtension.SupportedNullhomotopy.point)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteRelativeExtension.SupportedNullhomotopy.point_over)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteRelativeExtension.SupportedNullhomotopy.rec)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteRelativeExtension.SupportedNullhomotopy.recOn)
  pure ()

theorem DaggerFiniteRelativeExtension.supportedNullhomotopy._simp_1 :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 9012 :=
  @(recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 9020)

theorem DaggerFiniteRelativeExtension.supportedNullhomotopy._simp_3.{v₁, v₂, u₁, u₂} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 11678 :=
  @(recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 11704)

theorem DaggerFiniteRelativeExtension.supportedNullhomotopy._proof_1.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 11886 :=
  @(recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 14466)

noncomputable def DaggerFiniteRelativeExtension.supportedNullhomotopy.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 11545
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 11545
        [arg0]}
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 11545
        [arg0, arg1])
    {arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 11545
        [arg0, arg1, arg2]}
    (arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 11545
        [arg0, arg1, arg2, arg3])
    [arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 11545
        [arg0, arg1, arg2, arg3, arg4]]
    (arg6 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 11545
        [arg0, arg1, arg2, arg3, arg4, arg5])
    (arg7 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 11545
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6])
    :
    recovered_closed_result_type%
      DaggerRecoveredFiniteRelativeExtensionData.jsonData 11545
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 11545 :=
    @(recovered_closed_expr%
      DaggerRecoveredFiniteRelativeExtensionData.jsonData 11565)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5 arg6 arg7

theorem DaggerFiniteRelativeExtension.finite_support_nullhomotopic.{u} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 8603 :=
  @(recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 8900)

theorem DaggerFiniteRelativeExtension.supportedNullhomotopy._simp_2.{u} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 8955 :=
  @(recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 8972)

