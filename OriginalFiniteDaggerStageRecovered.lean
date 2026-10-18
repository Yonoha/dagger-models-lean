import OriginalFiniteDaggerOrientedPlacementRecovered
import OriginalFiniteRelativeBoundaryPresentationRecovered
import FixedCategoryColimits
import OriginalRecoveredClosedExpressionApplication
import OriginalRecoveredFinitePrivateExpression
import OriginalRecoveredFiniteRelativeCellFoundationData

/-! Original FiniteDaggerStage, with unchanged closed types and values. -/

set_option autoImplicit false
set_option maxRecDepth 100000

noncomputable abbrev DaggerFiniteDaggerExtension.orderedHom.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 55185
        []}
    (arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 55185
        [arg0])
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 55185
        [arg0, arg1])
    :
    recovered_closed_result_type%
      DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 55185
      [arg0, arg1, arg2]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 55185 :=
    @(recovered_finite_private_expr%
      DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 55197)
  exact @f arg0 arg1 arg2

structure DaggerFiniteDaggerExtension.Stage.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 57264
        []}
    (arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 57264
        [arg0])
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 57264
        [arg0, arg1])
    {arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 57264
        [arg0, arg1, arg2]}
    {arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 57264
        [arg0, arg1, arg2, arg3]}
    {arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 57264
        [arg0, arg1, arg2, arg3, arg4]}
    {arg6 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 57264
        [arg0, arg1, arg2, arg3, arg4, arg5]}
    [arg7 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 57264
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6]]
    (arg8 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 57264
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7])
    (arg9 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 57264
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8])
    (arg10 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 57264
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9])
    :
      recovered_closed_result_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 57264
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10] where
  C :
    recovered_closed_binder_type%
      DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 51133
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10]
  phi :
    recovered_closed_binder_type%
      DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 51133
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, C]
  theta :
    recovered_closed_binder_type%
      DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 51133
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, C, phi]
  over :
    recovered_closed_binder_type%
      DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 51133
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, C, phi, theta]

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteDaggerExtension.Stage)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteDaggerExtension.Stage.C)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteDaggerExtension.Stage._sizeOf_1)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteDaggerExtension.Stage._sizeOf_inst)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteDaggerExtension.Stage.casesOn)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteDaggerExtension.Stage.ctorIdx)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteDaggerExtension.Stage.mk)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteDaggerExtension.Stage.mk._flat_ctor)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteDaggerExtension.Stage.mk.inj)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteDaggerExtension.Stage.mk.injEq)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteDaggerExtension.Stage.mk.noConfusion)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteDaggerExtension.Stage.mk.sizeOf_spec)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteDaggerExtension.Stage.noConfusion)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteDaggerExtension.Stage.noConfusionType)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteDaggerExtension.Stage.over)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteDaggerExtension.Stage.phi)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteDaggerExtension.Stage.rec)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteDaggerExtension.Stage.recOn)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteDaggerExtension.Stage.theta)
  pure ()

noncomputable def DaggerFiniteDaggerExtension.Stage.attach.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 49615
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 49615
        [arg0]}
    {arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 49615
        [arg0, arg1]}
    {arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 49615
        [arg0, arg1, arg2]}
    {arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 49615
        [arg0, arg1, arg2, arg3]}
    {arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 49615
        [arg0, arg1, arg2, arg3, arg4]}
    {arg6 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 49615
        [arg0, arg1, arg2, arg3, arg4, arg5]}
    [arg7 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 49615
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6]]
    {arg8 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 49615
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7]}
    {arg9 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 49615
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8]}
    {arg10 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 49615
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9]}
    (arg11 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 49615
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10])
    :
    recovered_closed_result_type%
      DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 49615
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 49615 :=
    @(recovered_finite_private_expr%
      DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 49657)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5 arg6 arg7 arg8 arg9 arg10 arg11

noncomputable abbrev DaggerFiniteDaggerExtension.Stage.boundary.{u, u_1}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 59096
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 59096
        [arg0]}
    {arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 59096
        [arg0, arg1]}
    {arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 59096
        [arg0, arg1, arg2]}
    {arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 59096
        [arg0, arg1, arg2, arg3]}
    {arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 59096
        [arg0, arg1, arg2, arg3, arg4]}
    [arg6 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 59096
        [arg0, arg1, arg2, arg3, arg4, arg5]]
    {arg7 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 59096
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6]}
    {arg8 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 59096
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7]}
    :
    recovered_closed_result_type%
      DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 59096
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 59096 :=
    @(recovered_finite_private_expr%
      DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 59107)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5 arg6 arg7 arg8

noncomputable abbrev DaggerFiniteDaggerExtension.Stage.freeBoundary.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 50147
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 50147
        [arg0]}
    {arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 50147
        [arg0, arg1]}
    {arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 50147
        [arg0, arg1, arg2]}
    {arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 50147
        [arg0, arg1, arg2, arg3]}
    {arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 50147
        [arg0, arg1, arg2, arg3, arg4]}
    [arg6 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 50147
        [arg0, arg1, arg2, arg3, arg4, arg5]]
    {arg7 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 50147
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6]}
    {arg8 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 50147
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7]}
    :
    recovered_closed_result_type%
      DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 50147
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 50147 :=
    @(recovered_finite_private_expr%
      DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 50172)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5 arg6 arg7 arg8

theorem DaggerFiniteDaggerExtension.Stage.nextObj._proof_1.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 58489 :=
  @(recovered_finite_private_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 58532)

noncomputable def DaggerFiniteDaggerExtension.Stage.nextObj.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 55479
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 55479
        [arg0]}
    {arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 55479
        [arg0, arg1]}
    {arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 55479
        [arg0, arg1, arg2]}
    {arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 55479
        [arg0, arg1, arg2, arg3]}
    {arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 55479
        [arg0, arg1, arg2, arg3, arg4]}
    {arg6 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 55479
        [arg0, arg1, arg2, arg3, arg4, arg5]}
    [arg7 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 55479
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6]]
    {arg8 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 55479
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7]}
    {arg9 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 55479
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8]}
    {arg10 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 55479
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9]}
    (arg11 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 55479
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10])
    :
    recovered_closed_result_type%
      DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 55479
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 55479 :=
    @(recovered_finite_private_expr%
      DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 55500)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5 arg6 arg7 arg8 arg9 arg10 arg11

noncomputable def DaggerFiniteDaggerExtension.Stage.cellLeg.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 58777
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 58777
        [arg0]}
    {arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 58777
        [arg0, arg1]}
    {arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 58777
        [arg0, arg1, arg2]}
    {arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 58777
        [arg0, arg1, arg2, arg3]}
    {arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 58777
        [arg0, arg1, arg2, arg3, arg4]}
    {arg6 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 58777
        [arg0, arg1, arg2, arg3, arg4, arg5]}
    [arg7 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 58777
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6]]
    {arg8 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 58777
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7]}
    {arg9 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 58777
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8]}
    {arg10 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 58777
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9]}
    (arg11 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 58777
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10])
    :
    recovered_closed_result_type%
      DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 58777
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 58777 :=
    @(recovered_finite_private_expr%
      DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 58798)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5 arg6 arg7 arg8 arg9 arg10 arg11

noncomputable def DaggerFiniteDaggerExtension.Stage.edge.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 49978
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 49978
        [arg0]}
    {arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 49978
        [arg0, arg1]}
    {arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 49978
        [arg0, arg1, arg2]}
    {arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 49978
        [arg0, arg1, arg2, arg3]}
    {arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 49978
        [arg0, arg1, arg2, arg3, arg4]}
    {arg6 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 49978
        [arg0, arg1, arg2, arg3, arg4, arg5]}
    [arg7 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 49978
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6]]
    {arg8 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 49978
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7]}
    {arg9 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 49978
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8]}
    {arg10 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 49978
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9]}
    (arg11 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 49978
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10])
    :
    recovered_closed_result_type%
      DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 49978
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 49978 :=
    @(recovered_finite_private_expr%
      DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 50079)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5 arg6 arg7 arg8 arg9 arg10 arg11

theorem DaggerFiniteDaggerExtension.Stage.nextTheta._proof_1.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 57879 :=
  @(recovered_finite_private_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 57897)

theorem DaggerFiniteDaggerExtension.Stage.nextTheta._proof_2.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 56888 :=
  @(recovered_finite_private_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 56902)

noncomputable def DaggerFiniteDaggerExtension.Stage.oldLeg.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 55156
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 55156
        [arg0]}
    {arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 55156
        [arg0, arg1]}
    {arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 55156
        [arg0, arg1, arg2]}
    {arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 55156
        [arg0, arg1, arg2, arg3]}
    {arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 55156
        [arg0, arg1, arg2, arg3, arg4]}
    {arg6 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 55156
        [arg0, arg1, arg2, arg3, arg4, arg5]}
    [arg7 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 55156
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6]]
    {arg8 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 55156
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7]}
    {arg9 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 55156
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8]}
    {arg10 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 55156
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9]}
    (arg11 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 55156
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10])
    :
    recovered_closed_result_type%
      DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 55156
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 55156 :=
    @(recovered_finite_private_expr%
      DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 55177)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5 arg6 arg7 arg8 arg9 arg10 arg11

noncomputable def DaggerFiniteDaggerExtension.Stage.square.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 51039
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 51039
        [arg0]}
    {arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 51039
        [arg0, arg1]}
    {arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 51039
        [arg0, arg1, arg2]}
    {arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 51039
        [arg0, arg1, arg2, arg3]}
    {arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 51039
        [arg0, arg1, arg2, arg3, arg4]}
    {arg6 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 51039
        [arg0, arg1, arg2, arg3, arg4, arg5]}
    [arg7 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 51039
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6]]
    {arg8 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 51039
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7]}
    {arg9 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 51039
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8]}
    {arg10 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 51039
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9]}
    (arg11 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 51039
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10])
    :
    recovered_closed_result_type%
      DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 51039
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 51039 :=
    @(recovered_finite_private_expr%
      DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 51073)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5 arg6 arg7 arg8 arg9 arg10 arg11

theorem DaggerFiniteDaggerExtension.Stage.strict_boundary.{u} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 55724 :=
  @(recovered_finite_private_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 55787)

theorem DaggerFiniteDaggerExtension.Stage.nextTheta._proof_3.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 57123 :=
  @(recovered_finite_private_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 57152)

noncomputable def DaggerFiniteDaggerExtension.Stage.nextTheta.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 57191
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 57191
        [arg0]}
    {arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 57191
        [arg0, arg1]}
    {arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 57191
        [arg0, arg1, arg2]}
    {arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 57191
        [arg0, arg1, arg2, arg3]}
    {arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 57191
        [arg0, arg1, arg2, arg3, arg4]}
    {arg6 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 57191
        [arg0, arg1, arg2, arg3, arg4, arg5]}
    [arg7 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 57191
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6]]
    {arg8 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 57191
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7]}
    {arg9 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 57191
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8]}
    {arg10 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 57191
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9]}
    (arg11 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 57191
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10])
    :
    recovered_closed_result_type%
      DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 57191
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 57191 :=
    @(recovered_finite_private_expr%
      DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 57253)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5 arg6 arg7 arg8 arg9 arg10 arg11

noncomputable def DaggerFiniteDaggerExtension.Stage.characteristic.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 55673
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 55673
        [arg0]}
    {arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 55673
        [arg0, arg1]}
    {arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 55673
        [arg0, arg1, arg2]}
    {arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 55673
        [arg0, arg1, arg2, arg3]}
    {arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 55673
        [arg0, arg1, arg2, arg3, arg4]}
    {arg6 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 55673
        [arg0, arg1, arg2, arg3, arg4, arg5]}
    [arg7 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 55673
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6]]
    {arg8 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 55673
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7]}
    {arg9 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 55673
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8]}
    {arg10 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 55673
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9]}
    (arg11 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 55673
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10])
    :
    recovered_closed_result_type%
      DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 55673
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 55673 :=
    @(recovered_finite_private_expr%
      DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 55691)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5 arg6 arg7 arg8 arg9 arg10 arg11

theorem DaggerFiniteDaggerExtension.Stage.over_relation.{u} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 57625 :=
  @(recovered_finite_private_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 57868)

noncomputable def DaggerFiniteDaggerExtension.Stage.nextPhi.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 58696
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 58696
        [arg0]}
    {arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 58696
        [arg0, arg1]}
    {arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 58696
        [arg0, arg1, arg2]}
    {arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 58696
        [arg0, arg1, arg2, arg3]}
    {arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 58696
        [arg0, arg1, arg2, arg3, arg4]}
    {arg6 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 58696
        [arg0, arg1, arg2, arg3, arg4, arg5]}
    [arg7 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 58696
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6]]
    {arg8 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 58696
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7]}
    {arg9 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 58696
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8]}
    {arg10 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 58696
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9]}
    (arg11 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 58696
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10])
    :
    recovered_closed_result_type%
      DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 58696
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 58696 :=
    @(recovered_finite_private_expr%
      DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 58723)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5 arg6 arg7 arg8 arg9 arg10 arg11

theorem DaggerFiniteDaggerExtension.Stage.inclusion_nextTheta.{u} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 59156 :=
  @(recovered_finite_private_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 59183)

theorem DaggerFiniteDaggerExtension.Stage.old_nextPhi.{u} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 57342 :=
  @(recovered_finite_private_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 57396)

theorem DaggerFiniteDaggerExtension.Stage.cell_nextTheta.{u} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 58655 :=
  @(recovered_finite_private_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 58682)

theorem DaggerFiniteDaggerExtension.orientedEquiv_right.{u} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 51186 :=
  @(recovered_finite_private_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 51373)

theorem DaggerFiniteDaggerExtension.Stage.cell_nextPhi.{u} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 57917 :=
  @(recovered_finite_private_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 57945)

theorem DaggerFiniteDaggerExtension.Stage.edge_over.{u} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 59368 :=
  @(recovered_finite_private_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 59504)

theorem DaggerFiniteDaggerExtension.Stage.next_over.{u} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 50234 :=
  @(recovered_finite_private_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 50787)

noncomputable def DaggerFiniteDaggerExtension.Stage.next.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 50810
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 50810
        [arg0]}
    {arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 50810
        [arg0, arg1]}
    {arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 50810
        [arg0, arg1, arg2]}
    {arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 50810
        [arg0, arg1, arg2, arg3]}
    {arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 50810
        [arg0, arg1, arg2, arg3, arg4]}
    {arg6 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 50810
        [arg0, arg1, arg2, arg3, arg4, arg5]}
    [arg7 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 50810
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6]]
    {arg8 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 50810
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7]}
    {arg9 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 50810
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8]}
    {arg10 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 50810
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9]}
    (arg11 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 50810
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10])
    :
    recovered_closed_result_type%
      DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 50810
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 50810 :=
    @(recovered_finite_private_expr%
      DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 50850)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5 arg6 arg7 arg8 arg9 arg10 arg11

theorem DaggerFiniteDaggerExtension.zeroStage._proof_1.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 59821 :=
  @(recovered_finite_private_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 59832)

theorem DaggerFiniteDaggerExtension.zeroStage._proof_2.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 57982 :=
  @(recovered_finite_private_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 57996)

theorem DaggerFiniteDaggerExtension.zeroStage._proof_3.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 58096 :=
  @(recovered_finite_private_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 58415)

noncomputable def DaggerFiniteDaggerExtension.zeroStage.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 58578
        []}
    (arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 58578
        [arg0])
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 58578
        [arg0, arg1])
    {arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 58578
        [arg0, arg1, arg2]}
    {arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 58578
        [arg0, arg1, arg2, arg3]}
    {arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 58578
        [arg0, arg1, arg2, arg3, arg4]}
    {arg6 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 58578
        [arg0, arg1, arg2, arg3, arg4, arg5]}
    [arg7 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 58578
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6]]
    (arg8 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 58578
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7])
    (arg9 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 58578
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8])
    (arg10 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 58578
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9])
    (arg11 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 58578
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10])
    :
    recovered_closed_result_type%
      DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 58578
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 58578 :=
    @(recovered_finite_private_expr%
      DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 58640)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5 arg6 arg7 arg8 arg9 arg10 arg11

theorem DaggerFiniteDaggerExtension.Stage.cell_nextPhi_assoc.{u} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 58945 :=
  @(recovered_finite_private_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 59081)

theorem DaggerFiniteDaggerExtension.Stage.cell_nextTheta_assoc.{u} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 59261 :=
  @(recovered_finite_private_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 59356)

theorem DaggerFiniteDaggerExtension.Stage.old_nextPhi_assoc.{u} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 59568 :=
  @(recovered_finite_private_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 59660)

theorem DaggerFiniteDaggerExtension.Stage.inclusion_nextTheta_assoc.{u} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 59733 :=
  @(recovered_finite_private_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 59812)

