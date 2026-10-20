import OriginalSmithRecognitionRecovered
import OriginalSmithLimitsRecovered
import OriginalSmithPushoutsRecovered
import Mathlib.AlgebraicTopology.ModelCategory.Basic
import OriginalRecoveredClosedExpressionApplication
import OriginalRecoveredSmithModelConstructionData

/-! Original SmithModel, with unchanged closed types and values. -/

set_option autoImplicit false
set_option maxRecDepth 100000

structure DaggerSmithSolutionSet.CombinatorialData.{w, v, u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredSmithModelConstructionData.jsonData 16208
        []}
    [arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredSmithModelConstructionData.jsonData 16208
        [arg0]]
    {arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredSmithModelConstructionData.jsonData 16208
        [arg0, arg1]}
    {arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredSmithModelConstructionData.jsonData 16208
        [arg0, arg1, arg2]}
    (arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredSmithModelConstructionData.jsonData 16208
        [arg0, arg1, arg2, arg3])
    :
      recovered_closed_result_type%
        DaggerRecoveredSmithModelConstructionData.jsonData 16208
        [arg0, arg1, arg2, arg3, arg4] where
  locallyPresentable :
    recovered_closed_binder_type%
      DaggerRecoveredSmithModelConstructionData.jsonData 15316
      [arg0, arg1, arg2, arg3, arg4]
  smallI :
    recovered_closed_binder_type%
      DaggerRecoveredSmithModelConstructionData.jsonData 15316
      [arg0, arg1, arg2, arg3, arg4, locallyPresentable]
  smallJ :
    recovered_closed_binder_type%
      DaggerRecoveredSmithModelConstructionData.jsonData 15316
      [arg0, arg1, arg2, arg3, arg4, locallyPresentable, smallI]
  cardinalI :
    recovered_closed_binder_type%
      DaggerRecoveredSmithModelConstructionData.jsonData 15316
      [arg0, arg1, arg2, arg3, arg4, locallyPresentable, smallI, smallJ]
  cardinalJ :
    recovered_closed_binder_type%
      DaggerRecoveredSmithModelConstructionData.jsonData 15316
      [arg0, arg1, arg2, arg3, arg4, locallyPresentable, smallI, smallJ, cardinalI]
  trivialCofibrations :
    recovered_closed_binder_type%
      DaggerRecoveredSmithModelConstructionData.jsonData 15316
      [arg0, arg1, arg2, arg3, arg4, locallyPresentable, smallI, smallJ, cardinalI, cardinalJ]
  trivialFibrations :
    recovered_closed_binder_type%
      DaggerRecoveredSmithModelConstructionData.jsonData 15316
      [arg0, arg1, arg2, arg3, arg4, locallyPresentable, smallI, smallJ, cardinalI, cardinalJ,
       trivialCofibrations]
  fibrations :
    recovered_closed_binder_type%
      DaggerRecoveredSmithModelConstructionData.jsonData 15316
      [arg0, arg1, arg2, arg3, arg4, locallyPresentable, smallI, smallJ, cardinalI, cardinalJ,
       trivialCofibrations, trivialFibrations]
  cofFactorization :
    recovered_closed_binder_type%
      DaggerRecoveredSmithModelConstructionData.jsonData 15316
      [arg0, arg1, arg2, arg3, arg4, locallyPresentable, smallI, smallJ, cardinalI, cardinalJ,
       trivialCofibrations, trivialFibrations, fibrations]
  trivCofFactorization :
    recovered_closed_binder_type%
      DaggerRecoveredSmithModelConstructionData.jsonData 15316
      [arg0, arg1, arg2, arg3, arg4, locallyPresentable, smallI, smallJ, cardinalI, cardinalJ,
       trivialCofibrations, trivialFibrations, fibrations, cofFactorization]
  model :
    recovered_closed_binder_type%
      DaggerRecoveredSmithModelConstructionData.jsonData 15316
      [arg0, arg1, arg2, arg3, arg4, locallyPresentable, smallI, smallJ, cardinalI, cardinalJ,
       trivialCofibrations, trivialFibrations, fibrations, cofFactorization,
       trivCofFactorization]
  modelWeak :
    recovered_closed_binder_type%
      DaggerRecoveredSmithModelConstructionData.jsonData 15316
      [arg0, arg1, arg2, arg3, arg4, locallyPresentable, smallI, smallJ, cardinalI, cardinalJ,
       trivialCofibrations, trivialFibrations, fibrations, cofFactorization,
       trivCofFactorization, model]
  modelCof :
    recovered_closed_binder_type%
      DaggerRecoveredSmithModelConstructionData.jsonData 15316
      [arg0, arg1, arg2, arg3, arg4, locallyPresentable, smallI, smallJ, cardinalI, cardinalJ,
       trivialCofibrations, trivialFibrations, fibrations, cofFactorization,
       trivCofFactorization, model, modelWeak]
  modelFib :
    recovered_closed_binder_type%
      DaggerRecoveredSmithModelConstructionData.jsonData 15316
      [arg0, arg1, arg2, arg3, arg4, locallyPresentable, smallI, smallJ, cardinalI, cardinalJ,
       trivialCofibrations, trivialFibrations, fibrations, cofFactorization,
       trivCofFactorization, model, modelWeak, modelCof]

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerSmithSolutionSet.CombinatorialData)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerSmithSolutionSet.CombinatorialData._sizeOf_1)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerSmithSolutionSet.CombinatorialData._sizeOf_inst)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerSmithSolutionSet.CombinatorialData.cardinalI)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerSmithSolutionSet.CombinatorialData.cardinalJ)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerSmithSolutionSet.CombinatorialData.casesOn)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerSmithSolutionSet.CombinatorialData.cofFactorization)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerSmithSolutionSet.CombinatorialData.ctorIdx)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerSmithSolutionSet.CombinatorialData.fibrations)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerSmithSolutionSet.CombinatorialData.locallyPresentable)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerSmithSolutionSet.CombinatorialData.mk)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerSmithSolutionSet.CombinatorialData.mk._flat_ctor)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerSmithSolutionSet.CombinatorialData.mk.inj)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerSmithSolutionSet.CombinatorialData.mk.injEq)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerSmithSolutionSet.CombinatorialData.mk.noConfusion)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerSmithSolutionSet.CombinatorialData.mk.sizeOf_spec)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerSmithSolutionSet.CombinatorialData.model)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerSmithSolutionSet.CombinatorialData.modelCof)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerSmithSolutionSet.CombinatorialData.modelFib)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerSmithSolutionSet.CombinatorialData.modelWeak)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerSmithSolutionSet.CombinatorialData.noConfusion)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerSmithSolutionSet.CombinatorialData.noConfusionType)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerSmithSolutionSet.CombinatorialData.rec)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerSmithSolutionSet.CombinatorialData.recOn)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerSmithSolutionSet.CombinatorialData.smallI)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerSmithSolutionSet.CombinatorialData.smallJ)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerSmithSolutionSet.CombinatorialData.trivCofFactorization)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerSmithSolutionSet.CombinatorialData.trivialCofibrations)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerSmithSolutionSet.CombinatorialData.trivialFibrations)
  pure ()

theorem DaggerSmithSolutionSet.modelCategory._proof_2.{u_1, u_2} :
  recovered_closed_expr%
    DaggerRecoveredSmithModelConstructionData.jsonData 16230 :=
  @(recovered_closed_expr%
    DaggerRecoveredSmithModelConstructionData.jsonData 16240)

theorem DaggerSmithSolutionSet.modelCategory._proof_3.{u_1, u_2, u_3} :
  recovered_closed_expr%
    DaggerRecoveredSmithModelConstructionData.jsonData 16302 :=
  @(recovered_closed_expr%
    DaggerRecoveredSmithModelConstructionData.jsonData 16548)

theorem DaggerSmithSolutionSet.modelCategory._proof_1.{u_1, u_2, u_3} :
  recovered_closed_expr%
    DaggerRecoveredSmithModelConstructionData.jsonData 21991 :=
  @(recovered_closed_expr%
    DaggerRecoveredSmithModelConstructionData.jsonData 22002)

theorem DaggerSmithSolutionSet.modelCategory._proof_4.{u_1, u_2, u_3} :
  recovered_closed_expr%
    DaggerRecoveredSmithModelConstructionData.jsonData 22025 :=
  @(recovered_closed_expr%
    DaggerRecoveredSmithModelConstructionData.jsonData 22132)

noncomputable def DaggerSmithSolutionSet.modelCategory.{w, v, u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredSmithModelConstructionData.jsonData 16562
        []}
    [arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredSmithModelConstructionData.jsonData 16562
        [arg0]]
    [arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredSmithModelConstructionData.jsonData 16562
        [arg0, arg1]]
    {arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredSmithModelConstructionData.jsonData 16562
        [arg0, arg1, arg2]}
    {arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredSmithModelConstructionData.jsonData 16562
        [arg0, arg1, arg2, arg3]}
    [arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredSmithModelConstructionData.jsonData 16562
        [arg0, arg1, arg2, arg3, arg4]]
    (arg6 :
      recovered_closed_binder_type%
        DaggerRecoveredSmithModelConstructionData.jsonData 16562
        [arg0, arg1, arg2, arg3, arg4, arg5])
    [arg7 :
      recovered_closed_binder_type%
        DaggerRecoveredSmithModelConstructionData.jsonData 16562
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6]]
    [arg8 :
      recovered_closed_binder_type%
        DaggerRecoveredSmithModelConstructionData.jsonData 16562
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7]]
    (arg9 :
      recovered_closed_binder_type%
        DaggerRecoveredSmithModelConstructionData.jsonData 16562
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8])
    [arg10 :
      recovered_closed_binder_type%
        DaggerRecoveredSmithModelConstructionData.jsonData 16562
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9]]
    [arg11 :
      recovered_closed_binder_type%
        DaggerRecoveredSmithModelConstructionData.jsonData 16562
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10]]
    :
    recovered_closed_result_type%
      DaggerRecoveredSmithModelConstructionData.jsonData 16562
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredSmithModelConstructionData.jsonData 16562 :=
    @(recovered_closed_expr%
      DaggerRecoveredSmithModelConstructionData.jsonData 16636)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5 arg6 arg7 arg8 arg9 arg10 arg11

theorem DaggerSmithSolutionSet.model_weak.{w, v, u} :
  recovered_closed_expr%
    DaggerRecoveredSmithModelConstructionData.jsonData 17499 :=
  @(recovered_closed_expr%
    DaggerRecoveredSmithModelConstructionData.jsonData 17514)

theorem DaggerSmithSolutionSet.combinatorialData._proof_1.{u_1, u_2, u_3} :
  recovered_closed_expr%
    DaggerRecoveredSmithModelConstructionData.jsonData 21664 :=
  @(recovered_closed_expr%
    DaggerRecoveredSmithModelConstructionData.jsonData 21669)

theorem DaggerSmithSolutionSet.combinatorialData._proof_2.{u_1, u_2, u_3} :
  recovered_closed_expr%
    DaggerRecoveredSmithModelConstructionData.jsonData 22170 :=
  @(recovered_closed_expr%
    DaggerRecoveredSmithModelConstructionData.jsonData 22176)

theorem DaggerSmithSolutionSet.combinatorialData._proof_3.{u_1, u_2, u_3} :
  recovered_closed_expr%
    DaggerRecoveredSmithModelConstructionData.jsonData 22219 :=
  @(recovered_closed_expr%
    DaggerRecoveredSmithModelConstructionData.jsonData 22249)

theorem DaggerSmithSolutionSet.model_cof.{w, v, u} :
  recovered_closed_expr%
    DaggerRecoveredSmithModelConstructionData.jsonData 22737 :=
  @(recovered_closed_expr%
    DaggerRecoveredSmithModelConstructionData.jsonData 22750)

theorem DaggerSmithSolutionSet.model_fib.{w, v, u} :
  recovered_closed_expr%
    DaggerRecoveredSmithModelConstructionData.jsonData 23126 :=
  @(recovered_closed_expr%
    DaggerRecoveredSmithModelConstructionData.jsonData 23139)

noncomputable def DaggerSmithSolutionSet.combinatorialData.{w, v, u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredSmithModelConstructionData.jsonData 21686
        []}
    [arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredSmithModelConstructionData.jsonData 21686
        [arg0]]
    [arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredSmithModelConstructionData.jsonData 21686
        [arg0, arg1]]
    {arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredSmithModelConstructionData.jsonData 21686
        [arg0, arg1, arg2]}
    {arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredSmithModelConstructionData.jsonData 21686
        [arg0, arg1, arg2, arg3]}
    [arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredSmithModelConstructionData.jsonData 21686
        [arg0, arg1, arg2, arg3, arg4]]
    (arg6 :
      recovered_closed_binder_type%
        DaggerRecoveredSmithModelConstructionData.jsonData 21686
        [arg0, arg1, arg2, arg3, arg4, arg5])
    [arg7 :
      recovered_closed_binder_type%
        DaggerRecoveredSmithModelConstructionData.jsonData 21686
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6]]
    [arg8 :
      recovered_closed_binder_type%
        DaggerRecoveredSmithModelConstructionData.jsonData 21686
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7]]
    (arg9 :
      recovered_closed_binder_type%
        DaggerRecoveredSmithModelConstructionData.jsonData 21686
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8])
    [arg10 :
      recovered_closed_binder_type%
        DaggerRecoveredSmithModelConstructionData.jsonData 21686
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9]]
    [arg11 :
      recovered_closed_binder_type%
        DaggerRecoveredSmithModelConstructionData.jsonData 21686
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10]]
    :
    recovered_closed_result_type%
      DaggerRecoveredSmithModelConstructionData.jsonData 21686
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredSmithModelConstructionData.jsonData 21686 :=
    @(recovered_closed_expr%
      DaggerRecoveredSmithModelConstructionData.jsonData 21829)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5 arg6 arg7 arg8 arg9 arg10 arg11

