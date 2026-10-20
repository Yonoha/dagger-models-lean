import OriginalSSetFamilySigmaReconciledRecovered
import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
import OriginalRecoveredClosedExpressionApplication
import OriginalRecoveredBoundaryProductReconciliationData

/-! Original OriginalQuillenACells, with unchanged closed types and values. -/

set_option autoImplicit false
set_option maxRecDepth 100000

structure DaggerNerveTheoremA.Cell.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredBoundaryProductReconciliationData.jsonData 30871
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredBoundaryProductReconciliationData.jsonData 30871
        [arg0]}
    [arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredBoundaryProductReconciliationData.jsonData 30871
        [arg0, arg1]]
    [arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredBoundaryProductReconciliationData.jsonData 30871
        [arg0, arg1, arg2]]
    (arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredBoundaryProductReconciliationData.jsonData 30871
        [arg0, arg1, arg2, arg3])
    (arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredBoundaryProductReconciliationData.jsonData 30871
        [arg0, arg1, arg2, arg3, arg4])
    (arg6 :
      recovered_closed_binder_type%
        DaggerRecoveredBoundaryProductReconciliationData.jsonData 30871
        [arg0, arg1, arg2, arg3, arg4, arg5])
    :
      recovered_closed_result_type%
        DaggerRecoveredBoundaryProductReconciliationData.jsonData 30871
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6] where
  source :
    recovered_closed_binder_type%
      DaggerRecoveredBoundaryProductReconciliationData.jsonData 27973
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6]
  target :
    recovered_closed_binder_type%
      DaggerRecoveredBoundaryProductReconciliationData.jsonData 27973
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, source]
  bridge :
    recovered_closed_binder_type%
      DaggerRecoveredBoundaryProductReconciliationData.jsonData 27973
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, source, target]

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerNerveTheoremA.Cell)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerNerveTheoremA.Cell._sizeOf_1)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerNerveTheoremA.Cell._sizeOf_inst)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerNerveTheoremA.Cell.bridge)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerNerveTheoremA.Cell.casesOn)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerNerveTheoremA.Cell.ctorIdx)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerNerveTheoremA.Cell.mk)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerNerveTheoremA.Cell.mk._flat_ctor)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerNerveTheoremA.Cell.mk.inj)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerNerveTheoremA.Cell.mk.injEq)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerNerveTheoremA.Cell.mk.noConfusion)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerNerveTheoremA.Cell.mk.sizeOf_spec)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerNerveTheoremA.Cell.noConfusion)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerNerveTheoremA.Cell.noConfusionType)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerNerveTheoremA.Cell.rec)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerNerveTheoremA.Cell.recOn)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerNerveTheoremA.Cell.source)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerNerveTheoremA.Cell.target)
  pure ()

theorem DaggerNerveTheoremA.Cell.map._proof_1 :
  recovered_closed_expr%
    DaggerRecoveredBoundaryProductReconciliationData.jsonData 36768 :=
  @(recovered_closed_expr%
    DaggerRecoveredBoundaryProductReconciliationData.jsonData 36773)

theorem DaggerNerveTheoremA.Cell.map._proof_2 :
  recovered_closed_expr%
    DaggerRecoveredBoundaryProductReconciliationData.jsonData 13372 :=
  @(recovered_closed_expr%
    DaggerRecoveredBoundaryProductReconciliationData.jsonData 29694)

theorem DaggerNerveTheoremA.Cell.map._proof_3 :
  recovered_closed_expr%
    DaggerRecoveredBoundaryProductReconciliationData.jsonData 29346 :=
  @(recovered_closed_expr%
    DaggerRecoveredBoundaryProductReconciliationData.jsonData 29354)

noncomputable def DaggerNerveTheoremA.Cell.map.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredBoundaryProductReconciliationData.jsonData 36785
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredBoundaryProductReconciliationData.jsonData 36785
        [arg0]}
    [arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredBoundaryProductReconciliationData.jsonData 36785
        [arg0, arg1]]
    [arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredBoundaryProductReconciliationData.jsonData 36785
        [arg0, arg1, arg2]]
    (arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredBoundaryProductReconciliationData.jsonData 36785
        [arg0, arg1, arg2, arg3])
    {arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredBoundaryProductReconciliationData.jsonData 36785
        [arg0, arg1, arg2, arg3, arg4]}
    {arg6 :
      recovered_closed_binder_type%
        DaggerRecoveredBoundaryProductReconciliationData.jsonData 36785
        [arg0, arg1, arg2, arg3, arg4, arg5]}
    {arg7 :
      recovered_closed_binder_type%
        DaggerRecoveredBoundaryProductReconciliationData.jsonData 36785
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6]}
    {arg8 :
      recovered_closed_binder_type%
        DaggerRecoveredBoundaryProductReconciliationData.jsonData 36785
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7]}
    (arg9 :
      recovered_closed_binder_type%
        DaggerRecoveredBoundaryProductReconciliationData.jsonData 36785
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8])
    (arg10 :
      recovered_closed_binder_type%
        DaggerRecoveredBoundaryProductReconciliationData.jsonData 36785
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9])
    (arg11 :
      recovered_closed_binder_type%
        DaggerRecoveredBoundaryProductReconciliationData.jsonData 36785
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10])
    :
    recovered_closed_result_type%
      DaggerRecoveredBoundaryProductReconciliationData.jsonData 36785
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredBoundaryProductReconciliationData.jsonData 36785 :=
    @(recovered_closed_expr%
      DaggerRecoveredBoundaryProductReconciliationData.jsonData 36891)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5 arg6 arg7 arg8 arg9 arg10 arg11

theorem DaggerNerveTheoremA.Cell.ext.{u} :
  recovered_closed_expr%
    DaggerRecoveredBoundaryProductReconciliationData.jsonData 34013 :=
  @(recovered_closed_expr%
    DaggerRecoveredBoundaryProductReconciliationData.jsonData 35840)

theorem DaggerNerveTheoremA.Cell.map_id.{u} :
  recovered_closed_expr%
    DaggerRecoveredBoundaryProductReconciliationData.jsonData 29726 :=
  @(recovered_closed_expr%
    DaggerRecoveredBoundaryProductReconciliationData.jsonData 30010)

theorem DaggerNerveTheoremA.row._proof_1.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredBoundaryProductReconciliationData.jsonData 30900 :=
  @(recovered_closed_expr%
    DaggerRecoveredBoundaryProductReconciliationData.jsonData 30914)

theorem DaggerNerveTheoremA.Cell.map_comp._simp_1_1.{v₁, v₂, u₁, u₂} :
  recovered_closed_expr%
    DaggerRecoveredBoundaryProductReconciliationData.jsonData 30307 :=
  @(recovered_closed_expr%
    DaggerRecoveredBoundaryProductReconciliationData.jsonData 30333)

theorem DaggerNerveTheoremA.Cell.map_comp.{u} :
  recovered_closed_expr%
    DaggerRecoveredBoundaryProductReconciliationData.jsonData 35908 :=
  @(recovered_closed_expr%
    DaggerRecoveredBoundaryProductReconciliationData.jsonData 36744)

theorem DaggerNerveTheoremA.row._proof_2.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredBoundaryProductReconciliationData.jsonData 30075 :=
  @(recovered_closed_expr%
    DaggerRecoveredBoundaryProductReconciliationData.jsonData 30211)

noncomputable def DaggerNerveTheoremA.row.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredBoundaryProductReconciliationData.jsonData 28023
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredBoundaryProductReconciliationData.jsonData 28023
        [arg0]}
    [arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredBoundaryProductReconciliationData.jsonData 28023
        [arg0, arg1]]
    [arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredBoundaryProductReconciliationData.jsonData 28023
        [arg0, arg1, arg2]]
    (arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredBoundaryProductReconciliationData.jsonData 28023
        [arg0, arg1, arg2, arg3])
    (arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredBoundaryProductReconciliationData.jsonData 28023
        [arg0, arg1, arg2, arg3, arg4])
    :
    recovered_closed_result_type%
      DaggerRecoveredBoundaryProductReconciliationData.jsonData 28023
      [arg0, arg1, arg2, arg3, arg4, arg5]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredBoundaryProductReconciliationData.jsonData 28023 :=
    @(recovered_closed_expr%
      DaggerRecoveredBoundaryProductReconciliationData.jsonData 28068)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5

theorem DaggerNerveTheoremA.Cell.map_comm.{u} :
  recovered_closed_expr%
    DaggerRecoveredBoundaryProductReconciliationData.jsonData 29420 :=
  @(recovered_closed_expr%
    DaggerRecoveredBoundaryProductReconciliationData.jsonData 29692)

theorem DaggerNerveTheoremA.comparison._proof_2.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredBoundaryProductReconciliationData.jsonData 30618 :=
  @(recovered_closed_expr%
    DaggerRecoveredBoundaryProductReconciliationData.jsonData 30680)

theorem DaggerNerveTheoremA.comparison._proof_3.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredBoundaryProductReconciliationData.jsonData 30722 :=
  @(recovered_closed_expr%
    DaggerRecoveredBoundaryProductReconciliationData.jsonData 30866)

theorem DaggerNerveTheoremA.comparison._proof_1.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredBoundaryProductReconciliationData.jsonData 33890 :=
  @(recovered_closed_expr%
    DaggerRecoveredBoundaryProductReconciliationData.jsonData 33947)

theorem DaggerNerveTheoremA.comparison._proof_4.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredBoundaryProductReconciliationData.jsonData 33964 :=
  @(recovered_closed_expr%
    DaggerRecoveredBoundaryProductReconciliationData.jsonData 33974)

theorem DaggerNerveTheoremA.comparison._proof_5.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredBoundaryProductReconciliationData.jsonData 32461 :=
  @(recovered_closed_expr%
    DaggerRecoveredBoundaryProductReconciliationData.jsonData 33308)

noncomputable def DaggerNerveTheoremA.comparison.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredBoundaryProductReconciliationData.jsonData 30992
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredBoundaryProductReconciliationData.jsonData 30992
        [arg0]}
    [arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredBoundaryProductReconciliationData.jsonData 30992
        [arg0, arg1]]
    [arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredBoundaryProductReconciliationData.jsonData 30992
        [arg0, arg1, arg2]]
    (arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredBoundaryProductReconciliationData.jsonData 30992
        [arg0, arg1, arg2, arg3])
    :
    recovered_closed_result_type%
      DaggerRecoveredBoundaryProductReconciliationData.jsonData 30992
      [arg0, arg1, arg2, arg3, arg4]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredBoundaryProductReconciliationData.jsonData 30992 :=
    @(recovered_closed_expr%
      DaggerRecoveredBoundaryProductReconciliationData.jsonData 31050)
  exact @f arg0 arg1 arg2 arg3 arg4

theorem DaggerNerveTheoremA.Cell.ext_iff.{u} :
  recovered_closed_expr%
    DaggerRecoveredBoundaryProductReconciliationData.jsonData 33346 :=
  @(recovered_closed_expr%
    DaggerRecoveredBoundaryProductReconciliationData.jsonData 33844)

