import OriginalGlobalJCellCESUnifiedRecovered
import Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition
import OriginalRecoveredClosedExpressionApplication
import OriginalRecoveredFullGlobalJCellClosureData

/-! Original GlobalJCellWitnesses, with unchanged closed types and values. -/

set_option autoImplicit false
set_option maxRecDepth 100000

structure DaggerGlobalJCellTransfinite.OriginalWitness.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredFullGlobalJCellClosureData.jsonData 39589
        []}
    [arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredFullGlobalJCellClosureData.jsonData 39589
        [arg0]]
    [arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredFullGlobalJCellClosureData.jsonData 39589
        [arg0, arg1]]
    [arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredFullGlobalJCellClosureData.jsonData 39589
        [arg0, arg1, arg2]]
    [arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredFullGlobalJCellClosureData.jsonData 39589
        [arg0, arg1, arg2, arg3]]
    {arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredFullGlobalJCellClosureData.jsonData 39589
        [arg0, arg1, arg2, arg3, arg4]}
    {arg6 :
      recovered_closed_binder_type%
        DaggerRecoveredFullGlobalJCellClosureData.jsonData 39589
        [arg0, arg1, arg2, arg3, arg4, arg5]}
    {arg7 :
      recovered_closed_binder_type%
        DaggerRecoveredFullGlobalJCellClosureData.jsonData 39589
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6]}
    (arg8 :
      recovered_closed_binder_type%
        DaggerRecoveredFullGlobalJCellClosureData.jsonData 39589
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7])
    (arg9 :
      recovered_closed_binder_type%
        DaggerRecoveredFullGlobalJCellClosureData.jsonData 39589
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8])
    (arg10 :
      recovered_closed_binder_type%
        DaggerRecoveredFullGlobalJCellClosureData.jsonData 39589
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9])
    :
      recovered_closed_result_type%
        DaggerRecoveredFullGlobalJCellClosureData.jsonData 39589
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10] where
  stage :
    recovered_closed_binder_type%
      DaggerRecoveredFullGlobalJCellClosureData.jsonData 31577
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10]
  stageObject :
    recovered_closed_binder_type%
      DaggerRecoveredFullGlobalJCellClosureData.jsonData 31577
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, stage]
  leg_obj :
    recovered_closed_binder_type%
      DaggerRecoveredFullGlobalJCellClosureData.jsonData 31577
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, stage, stageObject]
  zeroObject :
    recovered_closed_binder_type%
      DaggerRecoveredFullGlobalJCellClosureData.jsonData 31577
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, stage, stageObject,
       leg_obj]
  stageClass :
    recovered_closed_binder_type%
      DaggerRecoveredFullGlobalJCellClosureData.jsonData 31577
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, stage, stageObject,
       leg_obj, zeroObject]
  stageCU :
    recovered_closed_binder_type%
      DaggerRecoveredFullGlobalJCellClosureData.jsonData 31577
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, stage, stageObject,
       leg_obj, zeroObject, stageClass]

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerGlobalJCellTransfinite.OriginalWitness)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerGlobalJCellTransfinite.OriginalWitness._sizeOf_1)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerGlobalJCellTransfinite.OriginalWitness._sizeOf_inst)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerGlobalJCellTransfinite.OriginalWitness.casesOn)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerGlobalJCellTransfinite.OriginalWitness.ctorIdx)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerGlobalJCellTransfinite.OriginalWitness.leg_obj)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerGlobalJCellTransfinite.OriginalWitness.mk)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerGlobalJCellTransfinite.OriginalWitness.mk._flat_ctor)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerGlobalJCellTransfinite.OriginalWitness.mk.inj)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerGlobalJCellTransfinite.OriginalWitness.mk.injEq)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerGlobalJCellTransfinite.OriginalWitness.mk.noConfusion)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerGlobalJCellTransfinite.OriginalWitness.mk.sizeOf_spec)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerGlobalJCellTransfinite.OriginalWitness.noConfusion)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerGlobalJCellTransfinite.OriginalWitness.noConfusionType)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerGlobalJCellTransfinite.OriginalWitness.rec)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerGlobalJCellTransfinite.OriginalWitness.recOn)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerGlobalJCellTransfinite.OriginalWitness.stage)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerGlobalJCellTransfinite.OriginalWitness.stageCU)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerGlobalJCellTransfinite.OriginalWitness.stageClass)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerGlobalJCellTransfinite.OriginalWitness.stageObject)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerGlobalJCellTransfinite.OriginalWitness.zeroObject)
  pure ()

theorem DaggerGlobalJCellTransfinite.originalWitness._proof_1.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredFullGlobalJCellClosureData.jsonData 31470 :=
  @(recovered_closed_expr%
    DaggerRecoveredFullGlobalJCellClosureData.jsonData 31479)

theorem DaggerGlobalJCellTransfinite.originalWitness._proof_2.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredFullGlobalJCellClosureData.jsonData 40471 :=
  @(recovered_closed_expr%
    DaggerRecoveredFullGlobalJCellClosureData.jsonData 41158)

noncomputable def DaggerGlobalJCellTransfinite.originalWitness.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredFullGlobalJCellClosureData.jsonData 30319
        []}
    [arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredFullGlobalJCellClosureData.jsonData 30319
        [arg0]]
    [arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredFullGlobalJCellClosureData.jsonData 30319
        [arg0, arg1]]
    [arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredFullGlobalJCellClosureData.jsonData 30319
        [arg0, arg1, arg2]]
    [arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredFullGlobalJCellClosureData.jsonData 30319
        [arg0, arg1, arg2, arg3]]
    {arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredFullGlobalJCellClosureData.jsonData 30319
        [arg0, arg1, arg2, arg3, arg4]}
    {arg6 :
      recovered_closed_binder_type%
        DaggerRecoveredFullGlobalJCellClosureData.jsonData 30319
        [arg0, arg1, arg2, arg3, arg4, arg5]}
    {arg7 :
      recovered_closed_binder_type%
        DaggerRecoveredFullGlobalJCellClosureData.jsonData 30319
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6]}
    (arg8 :
      recovered_closed_binder_type%
        DaggerRecoveredFullGlobalJCellClosureData.jsonData 30319
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7])
    (arg9 :
      recovered_closed_binder_type%
        DaggerRecoveredFullGlobalJCellClosureData.jsonData 30319
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8])
    (arg10 :
      recovered_closed_binder_type%
        DaggerRecoveredFullGlobalJCellClosureData.jsonData 30319
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9])
    (arg11 :
      recovered_closed_binder_type%
        DaggerRecoveredFullGlobalJCellClosureData.jsonData 30319
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10])
    :
    recovered_closed_result_type%
      DaggerRecoveredFullGlobalJCellClosureData.jsonData 30319
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredFullGlobalJCellClosureData.jsonData 30319 :=
    @(recovered_closed_expr%
      DaggerRecoveredFullGlobalJCellClosureData.jsonData 30357)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5 arg6 arg7 arg8 arg9 arg10 arg11

theorem DaggerGlobalJCellTransfinite.OriginalWitness.originalClass._proof_1.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredFullGlobalJCellClosureData.jsonData 40217 :=
  @(recovered_closed_expr%
    DaggerRecoveredFullGlobalJCellClosureData.jsonData 40233)

theorem DaggerGlobalJCellTransfinite.OriginalWitness.originalClass._proof_2.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredFullGlobalJCellClosureData.jsonData 31273 :=
  @(recovered_closed_expr%
    DaggerRecoveredFullGlobalJCellClosureData.jsonData 31297)

noncomputable def DaggerGlobalJCellTransfinite.OriginalWitness.source.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredFullGlobalJCellClosureData.jsonData 39566
        []}
    [arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredFullGlobalJCellClosureData.jsonData 39566
        [arg0]]
    [arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredFullGlobalJCellClosureData.jsonData 39566
        [arg0, arg1]]
    [arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredFullGlobalJCellClosureData.jsonData 39566
        [arg0, arg1, arg2]]
    [arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredFullGlobalJCellClosureData.jsonData 39566
        [arg0, arg1, arg2, arg3]]
    {arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredFullGlobalJCellClosureData.jsonData 39566
        [arg0, arg1, arg2, arg3, arg4]}
    {arg6 :
      recovered_closed_binder_type%
        DaggerRecoveredFullGlobalJCellClosureData.jsonData 39566
        [arg0, arg1, arg2, arg3, arg4, arg5]}
    {arg7 :
      recovered_closed_binder_type%
        DaggerRecoveredFullGlobalJCellClosureData.jsonData 39566
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6]}
    {arg8 :
      recovered_closed_binder_type%
        DaggerRecoveredFullGlobalJCellClosureData.jsonData 39566
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7]}
    {arg9 :
      recovered_closed_binder_type%
        DaggerRecoveredFullGlobalJCellClosureData.jsonData 39566
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8]}
    {arg10 :
      recovered_closed_binder_type%
        DaggerRecoveredFullGlobalJCellClosureData.jsonData 39566
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9]}
    (arg11 :
      recovered_closed_binder_type%
        DaggerRecoveredFullGlobalJCellClosureData.jsonData 39566
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10])
    :
    recovered_closed_result_type%
      DaggerRecoveredFullGlobalJCellClosureData.jsonData 39566
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredFullGlobalJCellClosureData.jsonData 39566 :=
    @(recovered_closed_expr%
      DaggerRecoveredFullGlobalJCellClosureData.jsonData 39578)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5 arg6 arg7 arg8 arg9 arg10 arg11

noncomputable def DaggerGlobalJCellTransfinite.OriginalWitness.originalClass.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredFullGlobalJCellClosureData.jsonData 40181
        []}
    [arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredFullGlobalJCellClosureData.jsonData 40181
        [arg0]]
    [arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredFullGlobalJCellClosureData.jsonData 40181
        [arg0, arg1]]
    [arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredFullGlobalJCellClosureData.jsonData 40181
        [arg0, arg1, arg2]]
    [arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredFullGlobalJCellClosureData.jsonData 40181
        [arg0, arg1, arg2, arg3]]
    {arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredFullGlobalJCellClosureData.jsonData 40181
        [arg0, arg1, arg2, arg3, arg4]}
    {arg6 :
      recovered_closed_binder_type%
        DaggerRecoveredFullGlobalJCellClosureData.jsonData 40181
        [arg0, arg1, arg2, arg3, arg4, arg5]}
    {arg7 :
      recovered_closed_binder_type%
        DaggerRecoveredFullGlobalJCellClosureData.jsonData 40181
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6]}
    {arg8 :
      recovered_closed_binder_type%
        DaggerRecoveredFullGlobalJCellClosureData.jsonData 40181
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7]}
    {arg9 :
      recovered_closed_binder_type%
        DaggerRecoveredFullGlobalJCellClosureData.jsonData 40181
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8]}
    {arg10 :
      recovered_closed_binder_type%
        DaggerRecoveredFullGlobalJCellClosureData.jsonData 40181
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9]}
    (arg11 :
      recovered_closed_binder_type%
        DaggerRecoveredFullGlobalJCellClosureData.jsonData 40181
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10])
    :
    recovered_closed_result_type%
      DaggerRecoveredFullGlobalJCellClosureData.jsonData 40181
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredFullGlobalJCellClosureData.jsonData 40181 :=
    @(recovered_closed_expr%
      DaggerRecoveredFullGlobalJCellClosureData.jsonData 40201)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5 arg6 arg7 arg8 arg9 arg10 arg11

theorem DaggerGlobalJCellTransfinite.OriginalWitness.originalClass_formula.{u} :
  recovered_closed_expr%
    DaggerRecoveredFullGlobalJCellClosureData.jsonData 35241 :=
  @(recovered_closed_expr%
    DaggerRecoveredFullGlobalJCellClosureData.jsonData 35328)

theorem DaggerGlobalJCellTransfinite.OriginalWitness.coherentlyUnitary.{u} :
  recovered_closed_expr%
    DaggerRecoveredFullGlobalJCellClosureData.jsonData 39672 :=
  @(recovered_closed_expr%
    DaggerRecoveredFullGlobalJCellClosureData.jsonData 39714)

noncomputable def DaggerGlobalJCellTransfinite.CES.{u}
    (arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredFullGlobalJCellClosureData.jsonData 41159
        [])
    :
    recovered_closed_result_type%
      DaggerRecoveredFullGlobalJCellClosureData.jsonData 41159
      [arg0]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredFullGlobalJCellClosureData.jsonData 41159 :=
    @(recovered_closed_expr%
      DaggerRecoveredFullGlobalJCellClosureData.jsonData 41166)
  exact @f arg0

theorem DaggerGlobalJCellTransfinite.ces_stable.{u} :
  recovered_closed_expr%
    DaggerRecoveredFullGlobalJCellClosureData.jsonData 39721 :=
  @(recovered_closed_expr%
    DaggerRecoveredFullGlobalJCellClosureData.jsonData 39831)
attribute [instance] DaggerGlobalJCellTransfinite.ces_stable

theorem DaggerGlobalJCellTransfinite.standard_ces_of_transfinite.{u} :
  recovered_closed_expr%
    DaggerRecoveredFullGlobalJCellClosureData.jsonData 39869 :=
  @(recovered_closed_expr%
    DaggerRecoveredFullGlobalJCellClosureData.jsonData 39882)

theorem DaggerGlobalJCellTransfinite.transfinite_ces_le.{u} :
  recovered_closed_expr%
    DaggerRecoveredFullGlobalJCellClosureData.jsonData 40240 :=
  @(recovered_closed_expr%
    DaggerRecoveredFullGlobalJCellClosureData.jsonData 40248)

