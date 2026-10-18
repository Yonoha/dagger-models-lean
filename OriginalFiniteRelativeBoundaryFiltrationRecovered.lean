import OriginalFiniteRelativeBoundaryProblemDefinitionsRecovered
import OriginalFiniteRelativeBoundaryCardRecovered
import Mathlib.Data.Fin.Tuple.Basic
import OriginalRecoveredClosedExpressionApplication
import OriginalRecoveredFinitePrivateExpression
import OriginalRecoveredFiniteRelativeCellFoundationData

/-! Original FiniteRelativeBoundaryFiltration, with unchanged closed types and values. -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace DaggerFiniteRelativeExtension
universe u

noncomputable def BoundaryFiltration.prependU {X : SSet.{u}}
    (A : SSet.Subcomplex X) (U : ℕ → SSet.Subcomplex X) : ℕ → SSet.Subcomplex X
  | 0 => A
  | n + 1 => U n

end DaggerFiniteRelativeExtension

structure DaggerFiniteRelativeExtension.BoundaryFiltration.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 31922
        []}
    (arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 31922
        [arg0])
    :
      recovered_closed_result_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 31922
        [arg0, arg1] where
  length :
    recovered_closed_binder_type%
      DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 34450
      [arg0, arg1]
  U :
    recovered_closed_binder_type%
      DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 34450
      [arg0, arg1, length]
  monotoneU :
    recovered_closed_binder_type%
      DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 34450
      [arg0, arg1, length, U]
  h0 :
    recovered_closed_binder_type%
      DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 34450
      [arg0, arg1, length, U, monotoneU]
  stop :
    recovered_closed_binder_type%
      DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 34450
      [arg0, arg1, length, U, monotoneU, h0]
  step :
    recovered_closed_binder_type%
      DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 34450
      [arg0, arg1, length, U, monotoneU, h0, stop]

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteRelativeExtension.BoundaryFiltration)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteRelativeExtension.BoundaryFiltration.U)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteRelativeExtension.BoundaryFiltration._sizeOf_1)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteRelativeExtension.BoundaryFiltration._sizeOf_inst)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteRelativeExtension.BoundaryFiltration.casesOn)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteRelativeExtension.BoundaryFiltration.ctorIdx)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteRelativeExtension.BoundaryFiltration.h0)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteRelativeExtension.BoundaryFiltration.length)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteRelativeExtension.BoundaryFiltration.mk)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteRelativeExtension.BoundaryFiltration.mk._flat_ctor)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteRelativeExtension.BoundaryFiltration.mk.inj)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteRelativeExtension.BoundaryFiltration.mk.injEq)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteRelativeExtension.BoundaryFiltration.mk.noConfusion)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteRelativeExtension.BoundaryFiltration.mk.sizeOf_spec)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteRelativeExtension.BoundaryFiltration.monotoneU)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteRelativeExtension.BoundaryFiltration.noConfusion)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteRelativeExtension.BoundaryFiltration.noConfusionType)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteRelativeExtension.BoundaryFiltration.rec)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteRelativeExtension.BoundaryFiltration.recOn)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteRelativeExtension.BoundaryFiltration.step)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteRelativeExtension.BoundaryFiltration.stop)
  pure ()

theorem DaggerFiniteRelativeExtension.BoundaryFiltration.prepend._proof_1 :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 32535 :=
  @(recovered_finite_private_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 32794)

theorem DaggerFiniteRelativeExtension.BoundaryFiltration.prepend._proof_4.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 32840 :=
  @(recovered_finite_private_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 33190)

theorem DaggerFiniteRelativeExtension.BoundaryFiltration.prepend._proof_5.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 34106 :=
  @(recovered_finite_private_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 34112)

theorem DaggerFiniteRelativeExtension.BoundaryFiltration.prepend._proof_2.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 37480 :=
  @(recovered_finite_private_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 37580)

theorem DaggerFiniteRelativeExtension.BoundaryFiltration.prepend._proof_3.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 37241 :=
  @(recovered_finite_private_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 37474)

theorem DaggerFiniteRelativeExtension.BoundaryFiltration.prepend._proof_6.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 37715 :=
  @(recovered_finite_private_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 37897)

theorem DaggerFiniteRelativeExtension.BoundaryFiltration.prepend._proof_7.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 34476 :=
  @(recovered_finite_private_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 34485)

theorem DaggerFiniteRelativeExtension.BoundaryFiltration.prepend._proof_8.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 34796 :=
  @(recovered_finite_private_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 34816)

noncomputable def DaggerFiniteRelativeExtension.BoundaryFiltration.prepend.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 32386
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 32386
        [arg0]}
    {arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 32386
        [arg0, arg1]}
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 32386
        [arg0, arg1, arg2])
    (arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 32386
        [arg0, arg1, arg2, arg3])
    :
    recovered_closed_result_type%
      DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 32386
      [arg0, arg1, arg2, arg3, arg4]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 32386 :=
    @(recovered_finite_private_expr%
      DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 32525)
  exact @f arg0 arg1 arg2 arg3 arg4

theorem DaggerFiniteRelativeExtension.BoundaryFiltration.exists_of_finite_complement.{u} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 33516 :=
  @(recovered_finite_private_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 34089)

theorem DaggerRecoveredFinitePrivate.prependUEq2.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 36135 :=
  @(recovered_finite_private_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 36142)

noncomputable abbrev DaggerRecoveredFinitePrivate.prependUSplitter.{u_1}
    (arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 36184
        [])
    (arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 36184
        [arg0])
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 36184
        [arg0, arg1])
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 36184
        [arg0, arg1, arg2])
    :
    recovered_closed_result_type%
      DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 36184
      [arg0, arg1, arg2, arg3]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 36184 :=
    @(recovered_finite_private_expr%
      DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 36125)
  exact @f arg0 arg1 arg2 arg3

theorem DaggerRecoveredFinitePrivate.prependUEq1.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 36214 :=
  @(recovered_finite_private_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 36219)

