import OriginalActualAcyclicGeneratorDefinitionsRecovered
import OriginalActualAcyclicGeneratorPropertiesRecovered
import OriginalActualGeneratingWeakRightLiftingRecovered
import OriginalUnitaryRealizationRecovered
import OriginalRecoveredClosedExpressionApplication
import OriginalRecoveredActualGlobalReverseLiftingData

/-! Original GlobalJRealization, with unchanged closed types and values. -/

set_option autoImplicit false
set_option maxRecDepth 100000

structure DaggerGlobalJLifting.RepresentativeRealizationData.{u}
    (arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredActualGlobalReverseLiftingData.jsonData 1203
        [])
    (arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredActualGlobalReverseLiftingData.jsonData 1203
        [arg0])
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredActualGlobalReverseLiftingData.jsonData 1203
        [arg0, arg1])
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredActualGlobalReverseLiftingData.jsonData 1203
        [arg0, arg1, arg2])
    :
      recovered_closed_result_type%
        DaggerRecoveredActualGlobalReverseLiftingData.jsonData 1203
        [arg0, arg1, arg2, arg3] where
  H :
    recovered_closed_binder_type%
      DaggerRecoveredActualGlobalReverseLiftingData.jsonData 1028
      [arg0, arg1, arg2, arg3]
  phi :
    recovered_closed_binder_type%
      DaggerRecoveredActualGlobalReverseLiftingData.jsonData 1028
      [arg0, arg1, arg2, arg3, H]
  hx :
    recovered_closed_binder_type%
      DaggerRecoveredActualGlobalReverseLiftingData.jsonData 1028
      [arg0, arg1, arg2, arg3, H, phi]
  hy :
    recovered_closed_binder_type%
      DaggerRecoveredActualGlobalReverseLiftingData.jsonData 1028
      [arg0, arg1, arg2, arg3, H, phi, hx]
  generator :
    recovered_closed_binder_type%
      DaggerRecoveredActualGlobalReverseLiftingData.jsonData 1028
      [arg0, arg1, arg2, arg3, H, phi, hx, hy]
  index :
    recovered_closed_binder_type%
      DaggerRecoveredActualGlobalReverseLiftingData.jsonData 1028
      [arg0, arg1, arg2, arg3, H, phi, hx, hy, generator]
  iso :
    recovered_closed_binder_type%
      DaggerRecoveredActualGlobalReverseLiftingData.jsonData 1028
      [arg0, arg1, arg2, arg3, H, phi, hx, hy, generator, index]
  underJ :
    recovered_closed_binder_type%
      DaggerRecoveredActualGlobalReverseLiftingData.jsonData 1028
      [arg0, arg1, arg2, arg3, H, phi, hx, hy, generator, index, iso]
  overI :
    recovered_closed_binder_type%
      DaggerRecoveredActualGlobalReverseLiftingData.jsonData 1028
      [arg0, arg1, arg2, arg3, H, phi, hx, hy, generator, index, iso, underJ]
  phiK :
    recovered_closed_binder_type%
      DaggerRecoveredActualGlobalReverseLiftingData.jsonData 1028
      [arg0, arg1, arg2, arg3, H, phi, hx, hy, generator, index, iso, underJ, overI]
  phiK_eq :
    recovered_closed_binder_type%
      DaggerRecoveredActualGlobalReverseLiftingData.jsonData 1028
      [arg0, arg1, arg2, arg3, H, phi, hx, hy, generator, index, iso, underJ, overI, phiK]
  hxK :
    recovered_closed_binder_type%
      DaggerRecoveredActualGlobalReverseLiftingData.jsonData 1028
      [arg0, arg1, arg2, arg3, H, phi, hx, hy, generator, index, iso, underJ, overI, phiK,
       phiK_eq]
  hyK :
    recovered_closed_binder_type%
      DaggerRecoveredActualGlobalReverseLiftingData.jsonData 1028
      [arg0, arg1, arg2, arg3, H, phi, hx, hy, generator, index, iso, underJ, overI, phiK,
       phiK_eq, hxK]
  J_leg :
    recovered_closed_binder_type%
      DaggerRecoveredActualGlobalReverseLiftingData.jsonData 1028
      [arg0, arg1, arg2, arg3, H, phi, hx, hy, generator, index, iso, underJ, overI, phiK,
       phiK_eq, hxK, hyK]
  generatorK :
    recovered_closed_binder_type%
      DaggerRecoveredActualGlobalReverseLiftingData.jsonData 1028
      [arg0, arg1, arg2, arg3, H, phi, hx, hy, generator, index, iso, underJ, overI, phiK,
       phiK_eq, hxK, hyK, J_leg]

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerGlobalJLifting.RepresentativeRealizationData)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerGlobalJLifting.RepresentativeRealizationData.H)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerGlobalJLifting.RepresentativeRealizationData.J_leg)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerGlobalJLifting.RepresentativeRealizationData._sizeOf_1)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerGlobalJLifting.RepresentativeRealizationData._sizeOf_inst)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerGlobalJLifting.RepresentativeRealizationData.casesOn)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerGlobalJLifting.RepresentativeRealizationData.ctorIdx)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerGlobalJLifting.RepresentativeRealizationData.generator)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerGlobalJLifting.RepresentativeRealizationData.generatorK)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerGlobalJLifting.RepresentativeRealizationData.hx)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerGlobalJLifting.RepresentativeRealizationData.hxK)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerGlobalJLifting.RepresentativeRealizationData.hy)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerGlobalJLifting.RepresentativeRealizationData.hyK)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerGlobalJLifting.RepresentativeRealizationData.index)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerGlobalJLifting.RepresentativeRealizationData.iso)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerGlobalJLifting.RepresentativeRealizationData.mk)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerGlobalJLifting.RepresentativeRealizationData.mk._flat_ctor)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerGlobalJLifting.RepresentativeRealizationData.mk.inj)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerGlobalJLifting.RepresentativeRealizationData.mk.injEq)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerGlobalJLifting.RepresentativeRealizationData.mk.noConfusion)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerGlobalJLifting.RepresentativeRealizationData.mk.sizeOf_spec)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerGlobalJLifting.RepresentativeRealizationData.noConfusion)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerGlobalJLifting.RepresentativeRealizationData.noConfusionType)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerGlobalJLifting.RepresentativeRealizationData.overI)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerGlobalJLifting.RepresentativeRealizationData.phi)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerGlobalJLifting.RepresentativeRealizationData.phiK)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerGlobalJLifting.RepresentativeRealizationData.phiK_eq)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerGlobalJLifting.RepresentativeRealizationData.rec)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerGlobalJLifting.RepresentativeRealizationData.recOn)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerGlobalJLifting.RepresentativeRealizationData.underJ)
  pure ()

noncomputable def DaggerGlobalJLifting.representativeSquare.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredActualGlobalReverseLiftingData.jsonData 1137
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredActualGlobalReverseLiftingData.jsonData 1137
        [arg0]}
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredActualGlobalReverseLiftingData.jsonData 1137
        [arg0, arg1])
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredActualGlobalReverseLiftingData.jsonData 1137
        [arg0, arg1, arg2])
    (arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredActualGlobalReverseLiftingData.jsonData 1137
        [arg0, arg1, arg2, arg3])
    (arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredActualGlobalReverseLiftingData.jsonData 1137
        [arg0, arg1, arg2, arg3, arg4])
    (arg6 :
      recovered_closed_binder_type%
        DaggerRecoveredActualGlobalReverseLiftingData.jsonData 1137
        [arg0, arg1, arg2, arg3, arg4, arg5])
    :
    recovered_closed_result_type%
      DaggerRecoveredActualGlobalReverseLiftingData.jsonData 1137
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredActualGlobalReverseLiftingData.jsonData 1137 :=
    @(recovered_closed_expr%
      DaggerRecoveredActualGlobalReverseLiftingData.jsonData 1198)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5 arg6

theorem DaggerGlobalJLifting.exists_representativeRealization.{u} :
  recovered_closed_expr%
    DaggerRecoveredActualGlobalReverseLiftingData.jsonData 15758 :=
  @(recovered_closed_expr%
    DaggerRecoveredActualGlobalReverseLiftingData.jsonData 16686)

noncomputable def DaggerGlobalJLifting.representativeRealization.{u}
    (arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredActualGlobalReverseLiftingData.jsonData 3479
        [])
    (arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredActualGlobalReverseLiftingData.jsonData 3479
        [arg0])
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredActualGlobalReverseLiftingData.jsonData 3479
        [arg0, arg1])
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredActualGlobalReverseLiftingData.jsonData 3479
        [arg0, arg1, arg2])
    (arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredActualGlobalReverseLiftingData.jsonData 3479
        [arg0, arg1, arg2, arg3])
    (arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredActualGlobalReverseLiftingData.jsonData 3479
        [arg0, arg1, arg2, arg3, arg4])
    (arg6 :
      recovered_closed_binder_type%
        DaggerRecoveredActualGlobalReverseLiftingData.jsonData 3479
        [arg0, arg1, arg2, arg3, arg4, arg5])
    (arg7 :
      recovered_closed_binder_type%
        DaggerRecoveredActualGlobalReverseLiftingData.jsonData 3479
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6])
    :
    recovered_closed_result_type%
      DaggerRecoveredActualGlobalReverseLiftingData.jsonData 3479
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredActualGlobalReverseLiftingData.jsonData 3479 :=
    @(recovered_closed_expr%
      DaggerRecoveredActualGlobalReverseLiftingData.jsonData 3499)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5 arg6 arg7

theorem DaggerGlobalJLifting.actualIntervalLift._proof_1.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredActualGlobalReverseLiftingData.jsonData 3652 :=
  @(recovered_closed_expr%
    DaggerRecoveredActualGlobalReverseLiftingData.jsonData 3725)

noncomputable def DaggerGlobalJLifting.actualIntervalLift.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredActualGlobalReverseLiftingData.jsonData 15728
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredActualGlobalReverseLiftingData.jsonData 15728
        [arg0]}
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredActualGlobalReverseLiftingData.jsonData 15728
        [arg0, arg1])
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredActualGlobalReverseLiftingData.jsonData 15728
        [arg0, arg1, arg2])
    (arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredActualGlobalReverseLiftingData.jsonData 15728
        [arg0, arg1, arg2, arg3])
    (arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredActualGlobalReverseLiftingData.jsonData 15728
        [arg0, arg1, arg2, arg3, arg4])
    (arg6 :
      recovered_closed_binder_type%
        DaggerRecoveredActualGlobalReverseLiftingData.jsonData 15728
        [arg0, arg1, arg2, arg3, arg4, arg5])
    (arg7 :
      recovered_closed_binder_type%
        DaggerRecoveredActualGlobalReverseLiftingData.jsonData 15728
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6])
    :
    recovered_closed_result_type%
      DaggerRecoveredActualGlobalReverseLiftingData.jsonData 15728
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredActualGlobalReverseLiftingData.jsonData 15728 :=
    @(recovered_closed_expr%
      DaggerRecoveredActualGlobalReverseLiftingData.jsonData 15748)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5 arg6 arg7

theorem DaggerGlobalJLifting.actualIntervalLift_left.{u} :
  recovered_closed_expr%
    DaggerRecoveredActualGlobalReverseLiftingData.jsonData 3818 :=
  @(recovered_closed_expr%
    DaggerRecoveredActualGlobalReverseLiftingData.jsonData 3864)

theorem DaggerGlobalJLifting.actualIntervalLift_right.{u} :
  recovered_closed_expr%
    DaggerRecoveredActualGlobalReverseLiftingData.jsonData 16932 :=
  @(recovered_closed_expr%
    DaggerRecoveredActualGlobalReverseLiftingData.jsonData 17015)

