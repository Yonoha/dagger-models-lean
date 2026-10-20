import OriginalFiniteRelativeExtensionCompactRecovered
import OriginalFiniteRelativeBoundaryPresentationRecovered
import Mathlib.Topology.Category.TopCat.Sphere
import OriginalRecoveredClosedExpressionApplication
import OriginalRecoveredFiniteRelativeExtensionData

/-! Original FiniteRelativeExtension, with unchanged closed types and values. -/

set_option autoImplicit false
set_option maxRecDepth 100000

noncomputable def DaggerFiniteRelativeExtension.chosenFactorization.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 20366
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 20366
        [arg0]}
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 20366
        [arg0, arg1])
    :
    recovered_closed_result_type%
      DaggerRecoveredFiniteRelativeExtensionData.jsonData 20366
      [arg0, arg1, arg2]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 20366 :=
    @(recovered_closed_expr%
      DaggerRecoveredFiniteRelativeExtensionData.jsonData 20383)
  exact @f arg0 arg1 arg2

structure DaggerFiniteRelativeExtension.FiniteRelativeExtensionData.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 19383
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 19383
        [arg0]}
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 19383
        [arg0, arg1])
    {arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 19383
        [arg0, arg1, arg2]}
    (arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 19383
        [arg0, arg1, arg2, arg3])
    :
      recovered_closed_result_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 19383
        [arg0, arg1, arg2, arg3, arg4] where
  F :
    recovered_closed_binder_type%
      DaggerRecoveredFiniteRelativeExtensionData.jsonData 17790
      [arg0, arg1, arg2, arg3, arg4]
  finiteF :
    recovered_closed_binder_type%
      DaggerRecoveredFiniteRelativeExtensionData.jsonData 17790
      [arg0, arg1, arg2, arg3, arg4, F]
  nullhomotopy :
    recovered_closed_binder_type%
      DaggerRecoveredFiniteRelativeExtensionData.jsonData 17790
      [arg0, arg1, arg2, arg3, arg4, F, finiteF]

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteRelativeExtension.FiniteRelativeExtensionData)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteRelativeExtension.FiniteRelativeExtensionData.F)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteRelativeExtension.FiniteRelativeExtensionData._sizeOf_1)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteRelativeExtension.FiniteRelativeExtensionData._sizeOf_inst)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteRelativeExtension.FiniteRelativeExtensionData.casesOn)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteRelativeExtension.FiniteRelativeExtensionData.ctorIdx)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteRelativeExtension.FiniteRelativeExtensionData.finiteF)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteRelativeExtension.FiniteRelativeExtensionData.mk)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteRelativeExtension.FiniteRelativeExtensionData.mk._flat_ctor)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteRelativeExtension.FiniteRelativeExtensionData.mk.inj)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteRelativeExtension.FiniteRelativeExtensionData.mk.injEq)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteRelativeExtension.FiniteRelativeExtensionData.mk.noConfusion)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteRelativeExtension.FiniteRelativeExtensionData.mk.sizeOf_spec)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteRelativeExtension.FiniteRelativeExtensionData.noConfusion)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteRelativeExtension.FiniteRelativeExtensionData.noConfusionType)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteRelativeExtension.FiniteRelativeExtensionData.nullhomotopy)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteRelativeExtension.FiniteRelativeExtensionData.rec)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteRelativeExtension.FiniteRelativeExtensionData.recOn)
  pure ()

theorem DaggerFiniteRelativeExtension.chosen_p_fibration.{u} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 19108 :=
  @(recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 19146)
attribute [instance] DaggerFiniteRelativeExtension.chosen_p_fibration

theorem DaggerFiniteRelativeExtension.chosen_p_weakEquivalence.{u} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 20603 :=
  @(recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 20610)
attribute [instance] DaggerFiniteRelativeExtension.chosen_p_weakEquivalence

theorem DaggerFiniteRelativeExtension.finiteRelativeExtension._proof_1.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 19544 :=
  @(recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 19876)

noncomputable def DaggerFiniteRelativeExtension.finiteRelativeExtension.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 19068
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 19068
        [arg0]}
    {arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 19068
        [arg0, arg1]}
    [arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 19068
        [arg0, arg1, arg2]]
    (arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 19068
        [arg0, arg1, arg2, arg3])
    (arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 19068
        [arg0, arg1, arg2, arg3, arg4])
    (arg6 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 19068
        [arg0, arg1, arg2, arg3, arg4, arg5])
    :
    recovered_closed_result_type%
      DaggerRecoveredFiniteRelativeExtensionData.jsonData 19068
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 19068 :=
    @(recovered_closed_expr%
      DaggerRecoveredFiniteRelativeExtensionData.jsonData 19085)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5 arg6

noncomputable abbrev DaggerFiniteRelativeExtension.FiniteRelativeExtensionData.extension.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 20581
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 20581
        [arg0]}
    {arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 20581
        [arg0, arg1]}
    {arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 20581
        [arg0, arg1, arg2]}
    {arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 20581
        [arg0, arg1, arg2, arg3]}
    (arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 20581
        [arg0, arg1, arg2, arg3, arg4])
    :
    recovered_closed_result_type%
      DaggerRecoveredFiniteRelativeExtensionData.jsonData 20581
      [arg0, arg1, arg2, arg3, arg4, arg5]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 20581 :=
    @(recovered_closed_expr%
      DaggerRecoveredFiniteRelativeExtensionData.jsonData 20587)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5

noncomputable def DaggerFiniteRelativeExtension.FiniteRelativeExtensionData.j.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 20594
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 20594
        [arg0]}
    {arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 20594
        [arg0, arg1]}
    {arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 20594
        [arg0, arg1, arg2]}
    {arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 20594
        [arg0, arg1, arg2, arg3]}
    (arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 20594
        [arg0, arg1, arg2, arg3, arg4])
    :
    recovered_closed_result_type%
      DaggerRecoveredFiniteRelativeExtensionData.jsonData 20594
      [arg0, arg1, arg2, arg3, arg4, arg5]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 20594 :=
    @(recovered_closed_expr%
      DaggerRecoveredFiniteRelativeExtensionData.jsonData 20600)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5

noncomputable def DaggerFiniteRelativeExtension.FiniteRelativeExtensionData.q.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 20651
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 20651
        [arg0]}
    {arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 20651
        [arg0, arg1]}
    {arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 20651
        [arg0, arg1, arg2]}
    {arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 20651
        [arg0, arg1, arg2, arg3]}
    (arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 20651
        [arg0, arg1, arg2, arg3, arg4])
    :
    recovered_closed_result_type%
      DaggerRecoveredFiniteRelativeExtensionData.jsonData 20651
      [arg0, arg1, arg2, arg3, arg4, arg5]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 20651 :=
    @(recovered_closed_expr%
      DaggerRecoveredFiniteRelativeExtensionData.jsonData 20666)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5

theorem DaggerFiniteRelativeExtension.chosen_i_mono.{u} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 20300 :=
  @(recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 20312)
attribute [instance] DaggerFiniteRelativeExtension.chosen_i_mono

theorem DaggerFiniteRelativeExtension.FiniteRelativeExtensionData.instMonoSSetJ.{u} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 19344 :=
  @(recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 19365)
attribute [instance] DaggerFiniteRelativeExtension.FiniteRelativeExtensionData.instMonoSSetJ

theorem DaggerFiniteRelativeExtension.FiniteRelativeExtensionData.fac.{u} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 20186 :=
  @(recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 20201)

theorem DaggerFiniteRelativeExtension.FiniteRelativeExtensionData.finiteAdded.{u} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 20323 :=
  @(recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 20349)
attribute [instance] DaggerFiniteRelativeExtension.FiniteRelativeExtensionData.finiteAdded

noncomputable def DaggerFiniteRelativeExtension.FiniteRelativeExtensionData.presentation.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 19043
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 19043
        [arg0]}
    {arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 19043
        [arg0, arg1]}
    {arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 19043
        [arg0, arg1, arg2]}
    {arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 19043
        [arg0, arg1, arg2, arg3]}
    (arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 19043
        [arg0, arg1, arg2, arg3, arg4])
    :
    recovered_closed_result_type%
      DaggerRecoveredFiniteRelativeExtensionData.jsonData 19043
      [arg0, arg1, arg2, arg3, arg4, arg5]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 19043 :=
    @(recovered_closed_expr%
      DaggerRecoveredFiniteRelativeExtensionData.jsonData 19061)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5

theorem DaggerFiniteRelativeExtension.finite_relative_extension_of_compact.{u} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 17889 :=
  @(recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 18289)

theorem DaggerFiniteRelativeExtension.finite_relative_extension_of_sphere.{u} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 17703 :=
  @(recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 17738)

theorem DaggerFiniteRelativeExtension.FiniteRelativeExtensionData.j_ambient.{u} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 19399 :=
  @(recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 19407)

theorem DaggerFiniteRelativeExtension.FiniteRelativeExtensionData.j_ambient_assoc.{u} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 20427 :=
  @(recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 20495)

theorem DaggerFiniteRelativeExtension.FiniteRelativeExtensionData.fac_assoc.{u} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 20518 :=
  @(recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 20575)

