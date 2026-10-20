import OriginalFiniteDaggerNullhomotopyRecovered
import OriginalRecoveredClosedExpressionApplication
import OriginalRecoveredFiniteRelativeExtensionData

/-! Original FiniteDaggerExtension, with unchanged closed types and values. -/

set_option autoImplicit false
set_option maxRecDepth 100000

structure DaggerFiniteDaggerExtension.FiniteExtensionData.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 22988
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 22988
        [arg0]}
    {arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 22988
        [arg0, arg1]}
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 22988
        [arg0, arg1, arg2])
    (arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 22988
        [arg0, arg1, arg2, arg3])
    (arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 22988
        [arg0, arg1, arg2, arg3, arg4])
    {arg6 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 22988
        [arg0, arg1, arg2, arg3, arg4, arg5]}
    (arg7 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 22988
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6])
    [arg8 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 22988
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7]]
    (arg9 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 22988
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8])
    (arg10 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 22988
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9])
    (arg11 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 22988
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10])
    :
      recovered_closed_result_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 22988
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11] where
  position :
    recovered_closed_binder_type%
      DaggerRecoveredFiniteRelativeExtensionData.jsonData 61305
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11]
  chain :
    recovered_closed_binder_type%
      DaggerRecoveredFiniteRelativeExtensionData.jsonData 61305
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11, position]
  zero :
    recovered_closed_binder_type%
      DaggerRecoveredFiniteRelativeExtensionData.jsonData 61305
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11, position,
       chain]
  phiNat :
    recovered_closed_binder_type%
      DaggerRecoveredFiniteRelativeExtensionData.jsonData 61305
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11, position,
       chain, zero]
  phi_zero :
    recovered_closed_binder_type%
      DaggerRecoveredFiniteRelativeExtensionData.jsonData 61305
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11, position,
       chain, zero, phiNat]
  thetaNat :
    recovered_closed_binder_type%
      DaggerRecoveredFiniteRelativeExtensionData.jsonData 61305
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11, position,
       chain, zero, phiNat, phi_zero]
  theta_zero :
    recovered_closed_binder_type%
      DaggerRecoveredFiniteRelativeExtensionData.jsonData 61305
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11, position,
       chain, zero, phiNat, phi_zero, thetaNat]
  attach :
    recovered_closed_binder_type%
      DaggerRecoveredFiniteRelativeExtensionData.jsonData 61305
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11, position,
       chain, zero, phiNat, phi_zero, thetaNat, theta_zero]
  cellLeg :
    recovered_closed_binder_type%
      DaggerRecoveredFiniteRelativeExtensionData.jsonData 61305
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11, position,
       chain, zero, phiNat, phi_zero, thetaNat, theta_zero, attach]
  square :
    recovered_closed_binder_type%
      DaggerRecoveredFiniteRelativeExtensionData.jsonData 61305
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11, position,
       chain, zero, phiNat, phi_zero, thetaNat, theta_zero, attach, cellLeg]
  classify :
    recovered_closed_binder_type%
      DaggerRecoveredFiniteRelativeExtensionData.jsonData 61305
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11, position,
       chain, zero, phiNat, phi_zero, thetaNat, theta_zero, attach, cellLeg, square]
  edge :
    recovered_closed_binder_type%
      DaggerRecoveredFiniteRelativeExtensionData.jsonData 61305
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11, position,
       chain, zero, phiNat, phi_zero, thetaNat, theta_zero, attach, cellLeg, square, classify]
  strict_boundary :
    recovered_closed_binder_type%
      DaggerRecoveredFiniteRelativeExtensionData.jsonData 61305
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11, position,
       chain, zero, phiNat, phi_zero, thetaNat, theta_zero, attach, cellLeg, square, classify,
       edge]
  cell_theta :
    recovered_closed_binder_type%
      DaggerRecoveredFiniteRelativeExtensionData.jsonData 61305
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11, position,
       chain, zero, phiNat, phi_zero, thetaNat, theta_zero, attach, cellLeg, square, classify,
       edge, strict_boundary]
  over :
    recovered_closed_binder_type%
      DaggerRecoveredFiniteRelativeExtensionData.jsonData 61305
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11, position,
       chain, zero, phiNat, phi_zero, thetaNat, theta_zero, attach, cellLeg, square, classify,
       edge, strict_boundary, cell_theta]
  finalUP :
    recovered_closed_binder_type%
      DaggerRecoveredFiniteRelativeExtensionData.jsonData 61305
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11, position,
       chain, zero, phiNat, phi_zero, thetaNat, theta_zero, attach, cellLeg, square, classify,
       edge, strict_boundary, cell_theta, over]
  fac :
    recovered_closed_binder_type%
      DaggerRecoveredFiniteRelativeExtensionData.jsonData 61305
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11, position,
       chain, zero, phiNat, phi_zero, thetaNat, theta_zero, attach, cellLeg, square, classify,
       edge, strict_boundary, cell_theta, over, finalUP]
  inclusion :
    recovered_closed_binder_type%
      DaggerRecoveredFiniteRelativeExtensionData.jsonData 61305
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11, position,
       chain, zero, phiNat, phi_zero, thetaNat, theta_zero, attach, cellLeg, square, classify,
       edge, strict_boundary, cell_theta, over, finalUP, fac]
  final_over :
    recovered_closed_binder_type%
      DaggerRecoveredFiniteRelativeExtensionData.jsonData 61305
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11, position,
       chain, zero, phiNat, phi_zero, thetaNat, theta_zero, attach, cellLeg, square, classify,
       edge, strict_boundary, cell_theta, over, finalUP, fac, inclusion]
  cof :
    recovered_closed_binder_type%
      DaggerRecoveredFiniteRelativeExtensionData.jsonData 61305
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11, position,
       chain, zero, phiNat, phi_zero, thetaNat, theta_zero, attach, cellLeg, square, classify,
       edge, strict_boundary, cell_theta, over, finalUP, fac, inclusion, final_over]
  mono :
    recovered_closed_binder_type%
      DaggerRecoveredFiniteRelativeExtensionData.jsonData 61305
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11, position,
       chain, zero, phiNat, phi_zero, thetaNat, theta_zero, attach, cellLeg, square, classify,
       edge, strict_boundary, cell_theta, over, finalUP, fac, inclusion, final_over, cof]
  countable :
    recovered_closed_binder_type%
      DaggerRecoveredFiniteRelativeExtensionData.jsonData 61305
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11, position,
       chain, zero, phiNat, phi_zero, thetaNat, theta_zero, attach, cellLeg, square, classify,
       edge, strict_boundary, cell_theta, over, finalUP, fac, inclusion, final_over, cof, mono]

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteDaggerExtension.FiniteExtensionData)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteDaggerExtension.FiniteExtensionData._sizeOf_1)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteDaggerExtension.FiniteExtensionData._sizeOf_inst)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteDaggerExtension.FiniteExtensionData.attach)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteDaggerExtension.FiniteExtensionData.casesOn)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteDaggerExtension.FiniteExtensionData.cellLeg)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteDaggerExtension.FiniteExtensionData.cell_theta)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteDaggerExtension.FiniteExtensionData.chain)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteDaggerExtension.FiniteExtensionData.classify)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteDaggerExtension.FiniteExtensionData.cof)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteDaggerExtension.FiniteExtensionData.countable)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteDaggerExtension.FiniteExtensionData.ctorIdx)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteDaggerExtension.FiniteExtensionData.edge)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteDaggerExtension.FiniteExtensionData.fac)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteDaggerExtension.FiniteExtensionData.finalUP)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteDaggerExtension.FiniteExtensionData.final_over)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteDaggerExtension.FiniteExtensionData.inclusion)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteDaggerExtension.FiniteExtensionData.mk)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteDaggerExtension.FiniteExtensionData.mk._flat_ctor)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteDaggerExtension.FiniteExtensionData.mk.inj)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteDaggerExtension.FiniteExtensionData.mk.injEq)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteDaggerExtension.FiniteExtensionData.mk.noConfusion)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteDaggerExtension.FiniteExtensionData.mk.sizeOf_spec)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteDaggerExtension.FiniteExtensionData.mono)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteDaggerExtension.FiniteExtensionData.noConfusion)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteDaggerExtension.FiniteExtensionData.noConfusionType)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteDaggerExtension.FiniteExtensionData.over)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteDaggerExtension.FiniteExtensionData.phiNat)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteDaggerExtension.FiniteExtensionData.phi_zero)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteDaggerExtension.FiniteExtensionData.position)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteDaggerExtension.FiniteExtensionData.rec)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteDaggerExtension.FiniteExtensionData.recOn)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteDaggerExtension.FiniteExtensionData.square)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteDaggerExtension.FiniteExtensionData.strict_boundary)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteDaggerExtension.FiniteExtensionData.thetaNat)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteDaggerExtension.FiniteExtensionData.theta_zero)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteDaggerExtension.FiniteExtensionData.zero)
  pure ()

noncomputable abbrev DaggerFiniteDaggerExtension.FiniteExtensionData.target.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 23108
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 23108
        [arg0]}
    {arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 23108
        [arg0, arg1]}
    {arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 23108
        [arg0, arg1, arg2]}
    {arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 23108
        [arg0, arg1, arg2, arg3]}
    {arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 23108
        [arg0, arg1, arg2, arg3, arg4]}
    {arg6 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 23108
        [arg0, arg1, arg2, arg3, arg4, arg5]}
    {arg7 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 23108
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6]}
    [arg8 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 23108
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7]]
    {arg9 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 23108
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8]}
    {arg10 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 23108
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9]}
    {arg11 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 23108
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10]}
    (arg12 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 23108
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11])
    :
    recovered_closed_result_type%
      DaggerRecoveredFiniteRelativeExtensionData.jsonData 23108
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11, arg12]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 23108 :=
    @(recovered_closed_expr%
      DaggerRecoveredFiniteRelativeExtensionData.jsonData 23123)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5 arg6 arg7 arg8 arg9 arg10 arg11 arg12

theorem DaggerFiniteDaggerExtension.FiniteExtensionData.kappa._proof_1.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 62785 :=
  @(recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 62796)

theorem DaggerFiniteDaggerExtension.FiniteExtensionData.kappa._proof_2.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 66615 :=
  @(recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 66653)

noncomputable def DaggerFiniteDaggerExtension.FiniteExtensionData.kappa.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 24592
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 24592
        [arg0]}
    {arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 24592
        [arg0, arg1]}
    {arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 24592
        [arg0, arg1, arg2]}
    {arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 24592
        [arg0, arg1, arg2, arg3]}
    {arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 24592
        [arg0, arg1, arg2, arg3, arg4]}
    {arg6 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 24592
        [arg0, arg1, arg2, arg3, arg4, arg5]}
    {arg7 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 24592
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6]}
    [arg8 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 24592
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7]]
    {arg9 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 24592
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8]}
    {arg10 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 24592
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9]}
    {arg11 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 24592
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10]}
    (arg12 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 24592
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11])
    :
    recovered_closed_result_type%
      DaggerRecoveredFiniteRelativeExtensionData.jsonData 24592
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11, arg12]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 24592 :=
    @(recovered_closed_expr%
      DaggerRecoveredFiniteRelativeExtensionData.jsonData 24638)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5 arg6 arg7 arg8 arg9 arg10 arg11 arg12

theorem DaggerFiniteDaggerExtension.FiniteExtensionData.theta._proof_1.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 62761 :=
  @(recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 62774)

theorem DaggerFiniteDaggerExtension.FiniteExtensionData.theta._proof_2.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 66672 :=
  @(recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 66685)

noncomputable def DaggerFiniteDaggerExtension.FiniteExtensionData.theta.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 29563
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 29563
        [arg0]}
    {arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 29563
        [arg0, arg1]}
    {arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 29563
        [arg0, arg1, arg2]}
    {arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 29563
        [arg0, arg1, arg2, arg3]}
    {arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 29563
        [arg0, arg1, arg2, arg3, arg4]}
    {arg6 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 29563
        [arg0, arg1, arg2, arg3, arg4, arg5]}
    {arg7 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 29563
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6]}
    [arg8 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 29563
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7]]
    {arg9 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 29563
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8]}
    {arg10 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 29563
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9]}
    {arg11 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 29563
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10]}
    (arg12 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 29563
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11])
    :
    recovered_closed_result_type%
      DaggerRecoveredFiniteRelativeExtensionData.jsonData 29563
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11, arg12]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 29563 :=
    @(recovered_closed_expr%
      DaggerRecoveredFiniteRelativeExtensionData.jsonData 29643)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5 arg6 arg7 arg8 arg9 arg10 arg11 arg12

theorem DaggerFiniteDaggerExtension.FiniteExtensionData.j_theta.{u} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 65265 :=
  @(recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 65292)

theorem DaggerFiniteDaggerExtension.extension_nullhomotopic.{u} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 21644 :=
  @(recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 21699)

theorem DaggerFiniteDaggerExtension.ofOrdered._proof_16.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 39145 :=
  @(recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 39158)

theorem DaggerFiniteDaggerExtension.ofOrdered._proof_6.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 61246 :=
  @(recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 61259)

theorem DaggerFiniteDaggerExtension.ofOrdered._proof_3.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 60997 :=
  @(recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 61008)

theorem DaggerFiniteDaggerExtension.ofOrdered._proof_14.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 39090 :=
  @(recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 39102)

theorem DaggerFiniteDaggerExtension.ofOrdered._proof_17.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 22123 :=
  @(recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 22361)

theorem DaggerFiniteDaggerExtension.ofOrdered._proof_4.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 22446 :=
  @(recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 22458)

theorem DaggerFiniteDaggerExtension.ofOrdered._proof_1.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 23090 :=
  @(recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 23095)

theorem DaggerFiniteDaggerExtension.ofOrdered._proof_2.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 60945 :=
  @(recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 60949)

theorem DaggerFiniteDaggerExtension.ofOrdered._proof_5.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 23519 :=
  @(recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 23538)

theorem DaggerFiniteDaggerExtension.ofOrdered._proof_7.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 24495 :=
  @(recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 24515)

theorem DaggerFiniteDaggerExtension.ofOrdered._proof_8.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 30182 :=
  @(recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 30193)

theorem DaggerFiniteDaggerExtension.ofOrdered._proof_9.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 29818 :=
  @(recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 30092)

theorem DaggerFiniteDaggerExtension.ofOrdered._proof_10.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 38773 :=
  @(recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 38793)

theorem DaggerFiniteDaggerExtension.ofOrdered._proof_11.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 38944 :=
  @(recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 39076)

theorem DaggerFiniteDaggerExtension.ofOrdered._proof_12.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 65434 :=
  @(recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 65460)

theorem DaggerFiniteDaggerExtension.ofOrdered._proof_13.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 38851 :=
  @(recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 38877)

theorem DaggerFiniteDaggerExtension.ofOrdered._proof_15.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 61556 :=
  @(recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 61648)

theorem DaggerFiniteDaggerExtension.ofOrdered._proof_18.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 57414 :=
  @(recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 57451)

theorem DaggerFiniteDaggerExtension.ofOrdered._proof_19.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 23398 :=
  @(recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 23460)

noncomputable def DaggerFiniteDaggerExtension.ofOrdered.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 22550
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 22550
        [arg0]}
    {arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 22550
        [arg0, arg1]}
    {arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 22550
        [arg0, arg1, arg2]}
    (arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 22550
        [arg0, arg1, arg2, arg3])
    (arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 22550
        [arg0, arg1, arg2, arg3, arg4])
    (arg6 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 22550
        [arg0, arg1, arg2, arg3, arg4, arg5])
    {arg7 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 22550
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6]}
    [arg8 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 22550
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7]]
    (arg9 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 22550
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8])
    (arg10 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 22550
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9])
    (arg11 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 22550
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10])
    :
    recovered_closed_result_type%
      DaggerRecoveredFiniteRelativeExtensionData.jsonData 22550
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 22550 :=
    @(recovered_closed_expr%
      DaggerRecoveredFiniteRelativeExtensionData.jsonData 22944)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5 arg6 arg7 arg8 arg9 arg10 arg11

theorem DaggerFiniteDaggerExtension.FiniteExtensionData.cofibration.{u} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 23036 :=
  @(recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 23080)
attribute [instance] DaggerFiniteDaggerExtension.FiniteExtensionData.cofibration

noncomputable def DaggerFiniteDaggerExtension.FiniteExtensionData.psi.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 57466
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 57466
        [arg0]}
    {arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 57466
        [arg0, arg1]}
    {arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 57466
        [arg0, arg1, arg2]}
    {arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 57466
        [arg0, arg1, arg2, arg3]}
    {arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 57466
        [arg0, arg1, arg2, arg3, arg4]}
    {arg6 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 57466
        [arg0, arg1, arg2, arg3, arg4, arg5]}
    {arg7 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 57466
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6]}
    [arg8 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 57466
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7]]
    {arg9 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 57466
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8]}
    {arg10 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 57466
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9]}
    {arg11 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 57466
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10]}
    (arg12 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 57466
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11])
    :
    recovered_closed_result_type%
      DaggerRecoveredFiniteRelativeExtensionData.jsonData 57466
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11, arg12]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 57466 :=
    @(recovered_closed_expr%
      DaggerRecoveredFiniteRelativeExtensionData.jsonData 57480)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5 arg6 arg7 arg8 arg9 arg10 arg11 arg12

theorem DaggerFiniteDaggerExtension.FiniteExtensionData.theta_psi.{u} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 24022 :=
  @(recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 24049)

theorem DaggerFiniteDaggerExtension.sphereExtension._proof_1.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 24222 :=
  @(recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 24237)

theorem DaggerFiniteDaggerExtension.FiniteExtensionData.kappa_psi.{u} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 57859 :=
  @(recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 57886)

theorem DaggerFiniteDaggerExtension.FiniteExtensionData.kappa_psi_assoc.{u} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 24372 :=
  @(recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 24473)

theorem DaggerFiniteDaggerExtension.sphereExtension._proof_2.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 57218 :=
  @(recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 57233)

theorem DaggerFiniteDaggerExtension.sphereOrdinaryData._proof_1.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 60236 :=
  @(recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 60251)

theorem DaggerFiniteDaggerExtension.FiniteExtensionData.theta_psi_assoc.{u} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 60350 :=
  @(recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 60448)

noncomputable def DaggerFiniteDaggerExtension.finiteDaggerExtension.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 60523
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 60523
        [arg0]}
    {arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 60523
        [arg0, arg1]}
    {arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 60523
        [arg0, arg1, arg2]}
    (arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 60523
        [arg0, arg1, arg2, arg3])
    (arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 60523
        [arg0, arg1, arg2, arg3, arg4])
    (arg6 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 60523
        [arg0, arg1, arg2, arg3, arg4, arg5])
    {arg7 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 60523
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6]}
    [arg8 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 60523
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7]]
    (arg9 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 60523
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8])
    (arg10 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 60523
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9])
    (arg11 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 60523
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10])
    :
    recovered_closed_result_type%
      DaggerRecoveredFiniteRelativeExtensionData.jsonData 60523
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 60523 :=
    @(recovered_closed_expr%
      DaggerRecoveredFiniteRelativeExtensionData.jsonData 60890)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5 arg6 arg7 arg8 arg9 arg10 arg11

theorem DaggerFiniteDaggerExtension.FiniteExtensionData.j_theta_assoc.{u} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 61428 :=
  @(recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 61534)

noncomputable def DaggerFiniteDaggerExtension.extensionHomotopy.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 62661
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 62661
        [arg0]}
    {arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 62661
        [arg0, arg1]}
    {arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 62661
        [arg0, arg1, arg2]}
    {arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 62661
        [arg0, arg1, arg2, arg3]}
    {arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 62661
        [arg0, arg1, arg2, arg3, arg4]}
    {arg6 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 62661
        [arg0, arg1, arg2, arg3, arg4, arg5]}
    {arg7 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 62661
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6]}
    [arg8 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 62661
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7]]
    {arg9 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 62661
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8]}
    {arg10 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 62661
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9]}
    {arg11 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 62661
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10]}
    (arg12 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 62661
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11])
    {arg13 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 62661
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11, arg12]}
    (arg14 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 62661
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11, arg12, arg13])
    (arg15 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 62661
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11, arg12, arg13,
         arg14])
    (arg16 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 62661
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11, arg12, arg13,
         arg14, arg15])
    :
    recovered_closed_result_type%
      DaggerRecoveredFiniteRelativeExtensionData.jsonData 62661
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11, arg12, arg13,
       arg14, arg15, arg16]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 62661 :=
    @(recovered_closed_expr%
      DaggerRecoveredFiniteRelativeExtensionData.jsonData 62702)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5 arg6 arg7 arg8 arg9 arg10 arg11 arg12 arg13 arg14 arg15
    arg16

theorem DaggerFiniteDaggerExtension.FiniteExtensionData.countable_target.{u} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 63227 :=
  @(recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 63261)

noncomputable def DaggerFiniteDaggerExtension.sphereExtension.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 63648
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 63648
        [arg0]}
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 63648
        [arg0, arg1])
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 63648
        [arg0, arg1, arg2])
    (arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 63648
        [arg0, arg1, arg2, arg3])
    (arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 63648
        [arg0, arg1, arg2, arg3, arg4])
    (arg6 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 63648
        [arg0, arg1, arg2, arg3, arg4, arg5])
    (arg7 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 63648
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6])
    :
    recovered_closed_result_type%
      DaggerRecoveredFiniteRelativeExtensionData.jsonData 63648
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 63648 :=
    @(recovered_closed_expr%
      DaggerRecoveredFiniteRelativeExtensionData.jsonData 63687)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5 arg6 arg7

theorem DaggerFiniteDaggerExtension.sphereExtension_nullhomotopic.{u} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 63420 :=
  @(recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 63451)

noncomputable def DaggerFiniteDaggerExtension.sphereOrdinaryData.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 63573
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 63573
        [arg0]}
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 63573
        [arg0, arg1])
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 63573
        [arg0, arg1, arg2])
    (arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 63573
        [arg0, arg1, arg2, arg3])
    (arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 63573
        [arg0, arg1, arg2, arg3, arg4])
    (arg6 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 63573
        [arg0, arg1, arg2, arg3, arg4, arg5])
    (arg7 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 63573
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6])
    :
    recovered_closed_result_type%
      DaggerRecoveredFiniteRelativeExtensionData.jsonData 63573
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 63573 :=
    @(recovered_closed_expr%
      DaggerRecoveredFiniteRelativeExtensionData.jsonData 63591)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5 arg6 arg7

noncomputable def DaggerFiniteDaggerExtension.sphereFiniteExtension.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 63556
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 63556
        [arg0]}
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 63556
        [arg0, arg1])
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 63556
        [arg0, arg1, arg2])
    (arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 63556
        [arg0, arg1, arg2, arg3])
    (arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 63556
        [arg0, arg1, arg2, arg3, arg4])
    (arg6 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 63556
        [arg0, arg1, arg2, arg3, arg4, arg5])
    (arg7 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 63556
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6])
    :
    recovered_closed_result_type%
      DaggerRecoveredFiniteRelativeExtensionData.jsonData 63556
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 63556 :=
    @(recovered_closed_expr%
      DaggerRecoveredFiniteRelativeExtensionData.jsonData 63565)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5 arg6 arg7

theorem DaggerFiniteDaggerExtension.FiniteExtensionData.local_mono.{u} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 65347 :=
  @(recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 65378)

theorem DaggerFiniteDaggerExtension.sphere_finite_extension.{u} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 66158 :=
  @(recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 66438)

