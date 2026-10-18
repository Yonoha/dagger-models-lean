import OriginalUnitaryIntervalBasicRecovered
import Mathlib.Logic.Small.Basic
import Mathlib.Data.Quot
import OriginalRecoveredClosedExpressionApplication
import OriginalRecoveredUnitaryPrivateExpression
import OriginalRecoveredUnitaryModelFoundationData

/-! Original UnitaryIntervalClasses, with unchanged closed types and values. -/

set_option autoImplicit false
set_option maxRecDepth 100000

noncomputable def DaggerUnitaryInterval.Interval.IsIso.{u}
    (arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryModelFoundationData.jsonData 29204
        [])
    (arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryModelFoundationData.jsonData 29204
        [arg0])
    :
    recovered_closed_result_type%
      DaggerRecoveredUnitaryModelFoundationData.jsonData 29204
      [arg0, arg1]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 29204 :=
    @(recovered_unitary_private_expr%
      DaggerRecoveredUnitaryModelFoundationData.jsonData 29242)
  exact @f arg0 arg1

noncomputable abbrev DaggerUnitaryInterval.intervalIsoSetoid.match_1.{u_1}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryModelFoundationData.jsonData 31095
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryModelFoundationData.jsonData 31095
        [arg0]}
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryModelFoundationData.jsonData 31095
        [arg0, arg1])
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryModelFoundationData.jsonData 31095
        [arg0, arg1, arg2])
    (arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryModelFoundationData.jsonData 31095
        [arg0, arg1, arg2, arg3])
    :
    recovered_closed_result_type%
      DaggerRecoveredUnitaryModelFoundationData.jsonData 31095
      [arg0, arg1, arg2, arg3, arg4]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 31095 :=
    @(recovered_unitary_private_expr%
      DaggerRecoveredUnitaryModelFoundationData.jsonData 31187)
  exact @f arg0 arg1 arg2 arg3 arg4

theorem DaggerUnitaryInterval.intervalIsoSetoid._proof_1.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 31922 :=
  @(recovered_unitary_private_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 32554)

noncomputable def DaggerUnitaryInterval.intervalIsoSetoid.{u}
    :
    recovered_closed_result_type%
      DaggerRecoveredUnitaryModelFoundationData.jsonData 30272
      []
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 30272 :=
    @(recovered_unitary_private_expr%
      DaggerRecoveredUnitaryModelFoundationData.jsonData 30277)
  exact @f

noncomputable def DaggerUnitaryInterval.IntervalClasses.{u}
    :
    recovered_closed_result_type%
      DaggerRecoveredUnitaryModelFoundationData.jsonData 26092
      []
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 26092 :=
    @(recovered_unitary_private_expr%
      DaggerRecoveredUnitaryModelFoundationData.jsonData 28254)
  exact @f

structure DaggerUnitaryInterval.IntervalCode
    :
      recovered_closed_result_type%
        DaggerRecoveredUnitaryModelFoundationData.jsonData 19164
        [] where
  carrier :
    recovered_closed_binder_type%
      DaggerRecoveredUnitaryModelFoundationData.jsonData 31600
      []
  operator :
    recovered_closed_binder_type%
      DaggerRecoveredUnitaryModelFoundationData.jsonData 31600
      [carrier]
  identity :
    recovered_closed_binder_type%
      DaggerRecoveredUnitaryModelFoundationData.jsonData 31600
      [carrier, operator]
  composition :
    recovered_closed_binder_type%
      DaggerRecoveredUnitaryModelFoundationData.jsonData 31600
      [carrier, operator, identity]
  dagger :
    recovered_closed_binder_type%
      DaggerRecoveredUnitaryModelFoundationData.jsonData 31600
      [carrier, operator, identity, composition]
  generator :
    recovered_closed_binder_type%
      DaggerRecoveredUnitaryModelFoundationData.jsonData 31600
      [carrier, operator, identity, composition, dagger]

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerUnitaryInterval.IntervalCode)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerUnitaryInterval.IntervalCode._sizeOf_1)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerUnitaryInterval.IntervalCode._sizeOf_inst)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerUnitaryInterval.IntervalCode.carrier)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerUnitaryInterval.IntervalCode.casesOn)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerUnitaryInterval.IntervalCode.composition)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerUnitaryInterval.IntervalCode.ctorIdx)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerUnitaryInterval.IntervalCode.dagger)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerUnitaryInterval.IntervalCode.generator)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerUnitaryInterval.IntervalCode.identity)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerUnitaryInterval.IntervalCode.mk)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerUnitaryInterval.IntervalCode.mk._flat_ctor)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerUnitaryInterval.IntervalCode.mk.inj)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerUnitaryInterval.IntervalCode.mk.injEq)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerUnitaryInterval.IntervalCode.mk.noConfusion)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerUnitaryInterval.IntervalCode.mk.sizeOf_spec)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerUnitaryInterval.IntervalCode.noConfusion)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerUnitaryInterval.IntervalCode.noConfusionType)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerUnitaryInterval.IntervalCode.operator)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerUnitaryInterval.IntervalCode.rec)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerUnitaryInterval.IntervalCode.recOn)
  pure ()

noncomputable abbrev DaggerUnitaryInterval.HomAt.{u}
    (arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryModelFoundationData.jsonData 31762
        [])
    (arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryModelFoundationData.jsonData 31762
        [arg0])
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryModelFoundationData.jsonData 31762
        [arg0, arg1])
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryModelFoundationData.jsonData 31762
        [arg0, arg1, arg2])
    :
    recovered_closed_result_type%
      DaggerRecoveredUnitaryModelFoundationData.jsonData 31762
      [arg0, arg1, arg2, arg3]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 31762 :=
    @(recovered_unitary_private_expr%
      DaggerRecoveredUnitaryModelFoundationData.jsonData 31770)
  exact @f arg0 arg1 arg2 arg3

theorem DaggerUnitaryInterval.encode._proof_1.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 31284 :=
  @(recovered_unitary_private_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 31299)

noncomputable def DaggerUnitaryInterval.encode.{u}
    (arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryModelFoundationData.jsonData 29186
        [])
    (arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryModelFoundationData.jsonData 29186
        [arg0])
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryModelFoundationData.jsonData 29186
        [arg0, arg1])
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryModelFoundationData.jsonData 29186
        [arg0, arg1, arg2])
    (arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryModelFoundationData.jsonData 29186
        [arg0, arg1, arg2, arg3])
    :
    recovered_closed_result_type%
      DaggerRecoveredUnitaryModelFoundationData.jsonData 29186
      [arg0, arg1, arg2, arg3, arg4]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 29186 :=
    @(recovered_unitary_private_expr%
      DaggerRecoveredUnitaryModelFoundationData.jsonData 29202)
  exact @f arg0 arg1 arg2 arg3 arg4

theorem DaggerUnitaryInterval.Interval.homDegreeNonempty.{u} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 31306 :=
  @(recovered_unitary_private_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 31354)
attribute [instance] DaggerUnitaryInterval.Interval.homDegreeNonempty

theorem DaggerUnitaryInterval.decode._proof_1.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 35976 :=
  @(recovered_unitary_private_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 35985)

noncomputable def DaggerUnitaryInterval.decode.{u}
    (arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryModelFoundationData.jsonData 31615
        [])
    (arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryModelFoundationData.jsonData 31615
        [arg0])
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryModelFoundationData.jsonData 31615
        [arg0, arg1])
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryModelFoundationData.jsonData 31615
        [arg0, arg1, arg2])
    (arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryModelFoundationData.jsonData 31615
        [arg0, arg1, arg2, arg3])
    :
    recovered_closed_result_type%
      DaggerRecoveredUnitaryModelFoundationData.jsonData 31615
      [arg0, arg1, arg2, arg3, arg4]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 31615 :=
    @(recovered_unitary_private_expr%
      DaggerRecoveredUnitaryModelFoundationData.jsonData 31628)
  exact @f arg0 arg1 arg2 arg3 arg4

noncomputable def DaggerUnitaryInterval.intervalCode.{u}
    (arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryModelFoundationData.jsonData 31918
        [])
    :
    recovered_closed_result_type%
      DaggerRecoveredUnitaryModelFoundationData.jsonData 31918
      [arg0]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 31918 :=
    @(recovered_unitary_private_expr%
      DaggerRecoveredUnitaryModelFoundationData.jsonData 31919)
  exact @f arg0

noncomputable def DaggerUnitaryInterval.codeTransport.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryModelFoundationData.jsonData 32564
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryModelFoundationData.jsonData 32564
        [arg0]}
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryModelFoundationData.jsonData 32564
        [arg0, arg1])
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryModelFoundationData.jsonData 32564
        [arg0, arg1, arg2])
    (arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryModelFoundationData.jsonData 32564
        [arg0, arg1, arg2, arg3])
    (arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryModelFoundationData.jsonData 32564
        [arg0, arg1, arg2, arg3, arg4])
    (arg6 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryModelFoundationData.jsonData 32564
        [arg0, arg1, arg2, arg3, arg4, arg5])
    :
    recovered_closed_result_type%
      DaggerRecoveredUnitaryModelFoundationData.jsonData 32564
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 32564 :=
    @(recovered_unitary_private_expr%
      DaggerRecoveredUnitaryModelFoundationData.jsonData 32576)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5 arg6

theorem DaggerUnitaryInterval.encode_injective.{u} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 31702 :=
  @(recovered_unitary_private_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 31718)

theorem DaggerUnitaryInterval.encode_transport.{u} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 30813 :=
  @(recovered_unitary_private_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 30968)

theorem DaggerUnitaryInterval.decode_encode.{u} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 31648 :=
  @(recovered_unitary_private_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 31669)

theorem DaggerUnitaryInterval.transport_operator.{u} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 30489 :=
  @(recovered_unitary_private_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 30730)

theorem DaggerUnitaryInterval.codeHom._proof_1.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 31890 :=
  @(recovered_unitary_private_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 31917)

noncomputable def DaggerUnitaryInterval.codeHom.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryModelFoundationData.jsonData 29127
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryModelFoundationData.jsonData 29127
        [arg0]}
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryModelFoundationData.jsonData 29127
        [arg0, arg1])
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryModelFoundationData.jsonData 29127
        [arg0, arg1, arg2])
    (arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryModelFoundationData.jsonData 29127
        [arg0, arg1, arg2, arg3])
    :
    recovered_closed_result_type%
      DaggerRecoveredUnitaryModelFoundationData.jsonData 29127
      [arg0, arg1, arg2, arg3, arg4]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 29127 :=
    @(recovered_unitary_private_expr%
      DaggerRecoveredUnitaryModelFoundationData.jsonData 29154)
  exact @f arg0 arg1 arg2 arg3 arg4

theorem DaggerUnitaryInterval.codeIso._proof_2.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 29166 :=
  @(recovered_unitary_private_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 29176)

theorem DaggerUnitaryInterval.codeHom_identity.{u} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 36008 :=
  @(recovered_unitary_private_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 36179)

theorem DaggerUnitaryInterval.codeHom_composition.{u} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 32623 :=
  @(recovered_unitary_private_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 33148)

theorem DaggerUnitaryInterval.codeHom_dagger.{u} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 29756 :=
  @(recovered_unitary_private_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 30091)

theorem DaggerUnitaryInterval.codeFunctor._proof_1.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 31820 :=
  @(recovered_unitary_private_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 31825)

noncomputable def DaggerUnitaryInterval.codeFunctor.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryModelFoundationData.jsonData 31413
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryModelFoundationData.jsonData 31413
        [arg0]}
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryModelFoundationData.jsonData 31413
        [arg0, arg1])
    :
    recovered_closed_result_type%
      DaggerRecoveredUnitaryModelFoundationData.jsonData 31413
      [arg0, arg1, arg2]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 31413 :=
    @(recovered_unitary_private_expr%
      DaggerRecoveredUnitaryModelFoundationData.jsonData 31466)
  exact @f arg0 arg1 arg2

theorem DaggerUnitaryInterval.codeIso._proof_1.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 31632 :=
  @(recovered_unitary_private_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 31635)

theorem DaggerUnitaryInterval.transport_inverse.{u} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 35897 :=
  @(recovered_unitary_private_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 35964)

theorem DaggerUnitaryInterval.codeFunctor_inverse.{u} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 29306 :=
  @(recovered_unitary_private_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 29630)

theorem DaggerUnitaryInterval.codeIso._proof_3.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 29275 :=
  @(recovered_unitary_private_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 29282)

noncomputable def DaggerUnitaryInterval.codeIso.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryModelFoundationData.jsonData 31672
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryModelFoundationData.jsonData 31672
        [arg0]}
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryModelFoundationData.jsonData 31672
        [arg0, arg1])
    :
    recovered_closed_result_type%
      DaggerRecoveredUnitaryModelFoundationData.jsonData 31672
      [arg0, arg1, arg2]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 31672 :=
    @(recovered_unitary_private_expr%
      DaggerRecoveredUnitaryModelFoundationData.jsonData 31697)
  exact @f arg0 arg1 arg2

theorem DaggerUnitaryInterval.J_hom_ext.{u} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 33198 :=
  @(recovered_unitary_private_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 35881)

theorem DaggerUnitaryInterval.codeTransport_generator.{u} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 31213 :=
  @(recovered_unitary_private_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 31263)

theorem DaggerUnitaryInterval.code_eq_intervalIso.{u} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 30097 :=
  @(recovered_unitary_private_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 30270)

noncomputable def DaggerUnitaryInterval.classCode.{u}
    (arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryModelFoundationData.jsonData 31826
        [])
    :
    recovered_closed_result_type%
      DaggerRecoveredUnitaryModelFoundationData.jsonData 31826
      [arg0]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 31826 :=
    @(recovered_unitary_private_expr%
      DaggerRecoveredUnitaryModelFoundationData.jsonData 31828)
  exact @f arg0

theorem DaggerUnitaryInterval.classCode_injective.{u} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 30748 :=
  @(recovered_unitary_private_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 30788)

theorem DaggerUnitaryInterval.intervalClassesSmall.{u} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 30732 :=
  @(recovered_unitary_private_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 30744)
attribute [instance] DaggerUnitaryInterval.intervalClassesSmall

noncomputable def DaggerUnitaryInterval.representatives.{u}
    (arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryModelFoundationData.jsonData 30289
        [])
    :
    recovered_closed_result_type%
      DaggerRecoveredUnitaryModelFoundationData.jsonData 30289
      [arg0]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 30289 :=
    @(recovered_unitary_private_expr%
      DaggerRecoveredUnitaryModelFoundationData.jsonData 30320)
  exact @f arg0

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerUnitaryInterval.intervalCode.eq_1)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerUnitaryInterval.representatives.eq_1)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerUnitaryInterval.codeTransport.congr_simp)
  pure ()

theorem DaggerUnitaryInterval.representatives_complete.{u} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 31472 :=
  @(recovered_unitary_private_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 31553)

