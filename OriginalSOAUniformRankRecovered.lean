import OriginalRLPFunctorsRecovered
import OriginalSmithCardinalRecovered
import OriginalRecoveredClosedExpressionApplication
import OriginalRecoveredSOAAccessibilityData

/-! Original SOAUniformRank, with unchanged closed types and values. -/

set_option autoImplicit false
set_option maxRecDepth 100000

structure DaggerSOAStepAccessible.CommonRank.{w, v, u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredSOAAccessibilityData.jsonData 40424
        []}
    [arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredSOAAccessibilityData.jsonData 40424
        [arg0]]
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredSOAAccessibilityData.jsonData 40424
        [arg0, arg1])
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredSOAAccessibilityData.jsonData 40424
        [arg0, arg1, arg2])
    :
      recovered_closed_result_type%
        DaggerRecoveredSOAAccessibilityData.jsonData 40424
        [arg0, arg1, arg2, arg3] where
  κ :
    recovered_closed_binder_type%
      DaggerRecoveredSOAAccessibilityData.jsonData 40322
      [arg0, arg1, arg2, arg3]
  regular :
    recovered_closed_binder_type%
      DaggerRecoveredSOAAccessibilityData.jsonData 40322
      [arg0, arg1, arg2, arg3, κ]
  aleph0_le :
    recovered_closed_binder_type%
      DaggerRecoveredSOAAccessibilityData.jsonData 40322
      [arg0, arg1, arg2, arg3, κ, regular]
  bot :
    recovered_closed_binder_type%
      DaggerRecoveredSOAAccessibilityData.jsonData 40322
      [arg0, arg1, arg2, arg3, κ, regular, aleph0_le]
  sourceP :
    recovered_closed_binder_type%
      DaggerRecoveredSOAAccessibilityData.jsonData 40322
      [arg0, arg1, arg2, arg3, κ, regular, aleph0_le, bot]
  targetP :
    recovered_closed_binder_type%
      DaggerRecoveredSOAAccessibilityData.jsonData 40322
      [arg0, arg1, arg2, arg3, κ, regular, aleph0_le, bot, sourceP]
  sourceQ :
    recovered_closed_binder_type%
      DaggerRecoveredSOAAccessibilityData.jsonData 40322
      [arg0, arg1, arg2, arg3, κ, regular, aleph0_le, bot, sourceP, targetP]
  targetQ :
    recovered_closed_binder_type%
      DaggerRecoveredSOAAccessibilityData.jsonData 40322
      [arg0, arg1, arg2, arg3, κ, regular, aleph0_le, bot, sourceP, targetP, sourceQ]
  suitableP :
    recovered_closed_binder_type%
      DaggerRecoveredSOAAccessibilityData.jsonData 40322
      [arg0, arg1, arg2, arg3, κ, regular, aleph0_le, bot, sourceP, targetP, sourceQ, targetQ]
  suitableQ :
    recovered_closed_binder_type%
      DaggerRecoveredSOAAccessibilityData.jsonData 40322
      [arg0, arg1, arg2, arg3, κ, regular, aleph0_le, bot, sourceP, targetP, sourceQ, targetQ,
       suitableP]

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerSOAStepAccessible.CommonRank)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerSOAStepAccessible.CommonRank._sizeOf_1)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerSOAStepAccessible.CommonRank._sizeOf_inst)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerSOAStepAccessible.CommonRank.aleph0_le)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerSOAStepAccessible.CommonRank.bot)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerSOAStepAccessible.CommonRank.casesOn)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerSOAStepAccessible.CommonRank.ctorIdx)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerSOAStepAccessible.CommonRank.mk)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerSOAStepAccessible.CommonRank.mk._flat_ctor)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerSOAStepAccessible.CommonRank.mk.inj)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerSOAStepAccessible.CommonRank.mk.injEq)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerSOAStepAccessible.CommonRank.mk.noConfusion)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerSOAStepAccessible.CommonRank.mk.sizeOf_spec)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerSOAStepAccessible.CommonRank.noConfusion)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerSOAStepAccessible.CommonRank.noConfusionType)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerSOAStepAccessible.CommonRank.rec)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerSOAStepAccessible.CommonRank.recOn)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerSOAStepAccessible.CommonRank.regular)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerSOAStepAccessible.CommonRank.sourceP)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerSOAStepAccessible.CommonRank.sourceQ)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerSOAStepAccessible.CommonRank.suitableP)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerSOAStepAccessible.CommonRank.suitableQ)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerSOAStepAccessible.CommonRank.targetP)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerSOAStepAccessible.CommonRank.targetQ)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerSOAStepAccessible.CommonRank.κ)
  pure ()

theorem DaggerSOAStepAccessible.commonRank._proof_1.{u_1, u_2, u_3} :
  recovered_closed_expr%
    DaggerRecoveredSOAAccessibilityData.jsonData 41175 :=
  @(recovered_closed_expr%
    DaggerRecoveredSOAAccessibilityData.jsonData 41182)

theorem DaggerSOAStepAccessible.commonRank._proof_2.{u_1, u_2, u_3} :
  recovered_closed_expr%
    DaggerRecoveredSOAAccessibilityData.jsonData 37432 :=
  @(recovered_closed_expr%
    DaggerRecoveredSOAAccessibilityData.jsonData 37443)

theorem DaggerSOAStepAccessible.commonRank._proof_6.{u_1, u_2, u_3} :
  recovered_closed_expr%
    DaggerRecoveredSOAAccessibilityData.jsonData 36635 :=
  @(recovered_closed_expr%
    DaggerRecoveredSOAAccessibilityData.jsonData 36653)

theorem DaggerSOAStepAccessible.commonRank._proof_3.{u_1, u_2, u_3} :
  recovered_closed_expr%
    DaggerRecoveredSOAAccessibilityData.jsonData 37091 :=
  @(recovered_closed_expr%
    DaggerRecoveredSOAAccessibilityData.jsonData 37360)

theorem DaggerSOAStepAccessible.commonRank._proof_11.{u_1, u_2, u_3} :
  recovered_closed_expr%
    DaggerRecoveredSOAAccessibilityData.jsonData 38805 :=
  @(recovered_closed_expr%
    DaggerRecoveredSOAAccessibilityData.jsonData 39087)

theorem DaggerSOAStepAccessible.commonRank._proof_5.{u_1, u_2, u_3} :
  recovered_closed_expr%
    DaggerRecoveredSOAAccessibilityData.jsonData 39664 :=
  @(recovered_closed_expr%
    DaggerRecoveredSOAAccessibilityData.jsonData 39718)

theorem DaggerSOAStepAccessible.commonRank._proof_4.{u_1, u_2, u_3} :
  recovered_closed_expr%
    DaggerRecoveredSOAAccessibilityData.jsonData 41315 :=
  @(recovered_closed_expr%
    DaggerRecoveredSOAAccessibilityData.jsonData 41445)

theorem DaggerSOAStepAccessible.commonRank._proof_7.{u_1, u_2, u_3} :
  recovered_closed_expr%
    DaggerRecoveredSOAAccessibilityData.jsonData 40410 :=
  @(recovered_closed_expr%
    DaggerRecoveredSOAAccessibilityData.jsonData 40419)

theorem DaggerSOAStepAccessible.commonRank._proof_8.{u_1, u_2, u_3} :
  recovered_closed_expr%
    DaggerRecoveredSOAAccessibilityData.jsonData 40334 :=
  @(recovered_closed_expr%
    DaggerRecoveredSOAAccessibilityData.jsonData 40363)

theorem DaggerSOAStepAccessible.commonRank._proof_9.{u_1, u_2, u_3} :
  recovered_closed_expr%
    DaggerRecoveredSOAAccessibilityData.jsonData 40375 :=
  @(recovered_closed_expr%
    DaggerRecoveredSOAAccessibilityData.jsonData 40391)

theorem DaggerSOAStepAccessible.commonRank._proof_10.{u_1, u_2, u_3} :
  recovered_closed_expr%
    DaggerRecoveredSOAAccessibilityData.jsonData 39757 :=
  @(recovered_closed_expr%
    DaggerRecoveredSOAAccessibilityData.jsonData 39774)

noncomputable def DaggerSOAStepAccessible.suitableOfEndpoints.{w, v, u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredSOAAccessibilityData.jsonData 40894
        []}
    [arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredSOAAccessibilityData.jsonData 40894
        [arg0]]
    [arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredSOAAccessibilityData.jsonData 40894
        [arg0, arg1]]
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredSOAAccessibilityData.jsonData 40894
        [arg0, arg1, arg2])
    [arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredSOAAccessibilityData.jsonData 40894
        [arg0, arg1, arg2, arg3]]
    (arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredSOAAccessibilityData.jsonData 40894
        [arg0, arg1, arg2, arg3, arg4])
    [arg6 :
      recovered_closed_binder_type%
        DaggerRecoveredSOAAccessibilityData.jsonData 40894
        [arg0, arg1, arg2, arg3, arg4, arg5]]
    [arg7 :
      recovered_closed_binder_type%
        DaggerRecoveredSOAAccessibilityData.jsonData 40894
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6]]
    [arg8 :
      recovered_closed_binder_type%
        DaggerRecoveredSOAAccessibilityData.jsonData 40894
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7]]
    :
    recovered_closed_result_type%
      DaggerRecoveredSOAAccessibilityData.jsonData 40894
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredSOAAccessibilityData.jsonData 40894 :=
    @(recovered_closed_expr%
      DaggerRecoveredSOAAccessibilityData.jsonData 41165)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5 arg6 arg7 arg8

theorem DaggerSOAStepAccessible.commonRank._proof_12.{u_1, u_2, u_3} :
  recovered_closed_expr%
    DaggerRecoveredSOAAccessibilityData.jsonData 40665 :=
  @(recovered_closed_expr%
    DaggerRecoveredSOAAccessibilityData.jsonData 40696)

theorem DaggerSOAStepAccessible.commonRank._proof_13.{u_1, u_2, u_3} :
  recovered_closed_expr%
    DaggerRecoveredSOAAccessibilityData.jsonData 39973 :=
  @(recovered_closed_expr%
    DaggerRecoveredSOAAccessibilityData.jsonData 40275)

noncomputable def DaggerSOAStepAccessible.commonRank.{w, v, u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredSOAAccessibilityData.jsonData 41462
        []}
    [arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredSOAAccessibilityData.jsonData 41462
        [arg0]]
    [arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredSOAAccessibilityData.jsonData 41462
        [arg0, arg1]]
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredSOAAccessibilityData.jsonData 41462
        [arg0, arg1, arg2])
    (arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredSOAAccessibilityData.jsonData 41462
        [arg0, arg1, arg2, arg3])
    [arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredSOAAccessibilityData.jsonData 41462
        [arg0, arg1, arg2, arg3, arg4]]
    [arg6 :
      recovered_closed_binder_type%
        DaggerRecoveredSOAAccessibilityData.jsonData 41462
        [arg0, arg1, arg2, arg3, arg4, arg5]]
    :
    recovered_closed_result_type%
      DaggerRecoveredSOAAccessibilityData.jsonData 41462
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredSOAAccessibilityData.jsonData 41462 :=
    @(recovered_closed_expr%
      DaggerRecoveredSOAAccessibilityData.jsonData 41829)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5 arg6

noncomputable def DaggerSOAStepAccessible.propertyRank.{w, v, u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredSOAAccessibilityData.jsonData 39732
        []}
    [arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredSOAAccessibilityData.jsonData 39732
        [arg0]]
    [arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredSOAAccessibilityData.jsonData 39732
        [arg0, arg1]]
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredSOAAccessibilityData.jsonData 39732
        [arg0, arg1, arg2])
    [arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredSOAAccessibilityData.jsonData 39732
        [arg0, arg1, arg2, arg3]]
    :
    recovered_closed_result_type%
      DaggerRecoveredSOAAccessibilityData.jsonData 39732
      [arg0, arg1, arg2, arg3, arg4]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredSOAAccessibilityData.jsonData 39732 :=
    @(recovered_closed_expr%
      DaggerRecoveredSOAAccessibilityData.jsonData 39745)
  exact @f arg0 arg1 arg2 arg3 arg4

