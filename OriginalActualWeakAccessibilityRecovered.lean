import OriginalActualWeakPredicatesRecovered
import OriginalRecoveredClosedExpressionApplication
import OriginalRecoveredActualWeakPipelineData

/-! Original ActualWeakAccessibility, with unchanged closed types and values. -/

set_option autoImplicit false
set_option maxRecDepth 100000

structure DaggerActualWeakAccessibility.AccessibilityData.{u, v, t}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredActualWeakPipelineData.jsonData 13602
        []}
    [arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredActualWeakPipelineData.jsonData 13602
        [arg0]]
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredActualWeakPipelineData.jsonData 13602
        [arg0, arg1])
    :
      recovered_closed_result_type%
        DaggerRecoveredActualWeakPipelineData.jsonData 13602
        [arg0, arg1, arg2] where
  κ :
    recovered_closed_binder_type%
      DaggerRecoveredActualWeakPipelineData.jsonData 9751
      [arg0, arg1, arg2]
  regular :
    recovered_closed_binder_type%
      DaggerRecoveredActualWeakPipelineData.jsonData 9751
      [arg0, arg1, arg2, κ]
  Q :
    recovered_closed_binder_type%
      DaggerRecoveredActualWeakPipelineData.jsonData 9751
      [arg0, arg1, arg2, κ, regular]
  small :
    recovered_closed_binder_type%
      DaggerRecoveredActualWeakPipelineData.jsonData 9751
      [arg0, arg1, arg2, κ, regular, Q]
  generator :
    recovered_closed_binder_type%
      DaggerRecoveredActualWeakPipelineData.jsonData 9751
      [arg0, arg1, arg2, κ, regular, Q, small]
  category :
    recovered_closed_binder_type%
      DaggerRecoveredActualWeakPipelineData.jsonData 9751
      [arg0, arg1, arg2, κ, regular, Q, small, generator]
  inclusion :
    recovered_closed_binder_type%
      DaggerRecoveredActualWeakPipelineData.jsonData 9751
      [arg0, arg1, arg2, κ, regular, Q, small, generator, category]

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerActualWeakAccessibility.AccessibilityData)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerActualWeakAccessibility.AccessibilityData.Q)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerActualWeakAccessibility.AccessibilityData._sizeOf_1)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerActualWeakAccessibility.AccessibilityData._sizeOf_inst)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerActualWeakAccessibility.AccessibilityData.casesOn)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerActualWeakAccessibility.AccessibilityData.category)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerActualWeakAccessibility.AccessibilityData.ctorIdx)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerActualWeakAccessibility.AccessibilityData.generator)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerActualWeakAccessibility.AccessibilityData.inclusion)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerActualWeakAccessibility.AccessibilityData.mk)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerActualWeakAccessibility.AccessibilityData.mk._flat_ctor)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerActualWeakAccessibility.AccessibilityData.mk.inj)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerActualWeakAccessibility.AccessibilityData.mk.injEq)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerActualWeakAccessibility.AccessibilityData.mk.noConfusion)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerActualWeakAccessibility.AccessibilityData.mk.sizeOf_spec)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerActualWeakAccessibility.AccessibilityData.noConfusion)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerActualWeakAccessibility.AccessibilityData.noConfusionType)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerActualWeakAccessibility.AccessibilityData.rec)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerActualWeakAccessibility.AccessibilityData.recOn)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerActualWeakAccessibility.AccessibilityData.regular)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerActualWeakAccessibility.AccessibilityData.small)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerActualWeakAccessibility.AccessibilityData.κ)
  pure ()

theorem DaggerActualWeakAccessibility.wg_accessibility.{u} :
  recovered_closed_expr%
    DaggerRecoveredActualWeakPipelineData.jsonData 11934 :=
  @(recovered_closed_expr%
    DaggerRecoveredActualWeakPipelineData.jsonData 12048)

theorem DaggerActualWeakAccessibility.wg_inclusion_accessible.{u} :
  recovered_closed_expr%
    DaggerRecoveredActualWeakPipelineData.jsonData 9780 :=
  @(recovered_closed_expr%
    DaggerRecoveredActualWeakPipelineData.jsonData 10131)

theorem DaggerActualWeakAccessibility.wg_category_accessible.{u} :
  recovered_closed_expr%
    DaggerRecoveredActualWeakPipelineData.jsonData 12596 :=
  @(recovered_closed_expr%
    DaggerRecoveredActualWeakPipelineData.jsonData 12666)

theorem DaggerActualWeakAccessibility.wd_accessibility.{u} :
  recovered_closed_expr%
    DaggerRecoveredActualWeakPipelineData.jsonData 11663 :=
  @(recovered_closed_expr%
    DaggerRecoveredActualWeakPipelineData.jsonData 11782)

theorem DaggerActualWeakAccessibility.wdData._proof_1.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredActualWeakPipelineData.jsonData 12914 :=
  @(recovered_closed_expr%
    DaggerRecoveredActualWeakPipelineData.jsonData 13235)

noncomputable def DaggerActualWeakAccessibility.wdData.{u}
    (arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredActualWeakPipelineData.jsonData 13239
        [])
    :
    recovered_closed_result_type%
      DaggerRecoveredActualWeakPipelineData.jsonData 13239
      [arg0]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredActualWeakPipelineData.jsonData 13239 :=
    @(recovered_closed_expr%
      DaggerRecoveredActualWeakPipelineData.jsonData 13244)
  exact @f arg0

theorem DaggerActualWeakAccessibility.wdRank_regular.{u} :
  recovered_closed_expr%
    DaggerRecoveredActualWeakPipelineData.jsonData 12708 :=
  @(recovered_closed_expr%
    DaggerRecoveredActualWeakPipelineData.jsonData 12711)
attribute [instance] DaggerActualWeakAccessibility.wdRank_regular

theorem DaggerActualWeakAccessibility.wd_generator_presentable.{u} :
  recovered_closed_expr%
    DaggerRecoveredActualWeakPipelineData.jsonData 11534 :=
  @(recovered_closed_expr%
    DaggerRecoveredActualWeakPipelineData.jsonData 11558)

theorem DaggerActualWeakAccessibility.wgData._proof_1.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredActualWeakPipelineData.jsonData 12209 :=
  @(recovered_closed_expr%
    DaggerRecoveredActualWeakPipelineData.jsonData 12548)

noncomputable def DaggerActualWeakAccessibility.wgData.{u}
    (arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredActualWeakPipelineData.jsonData 11607
        [])
    :
    recovered_closed_result_type%
      DaggerRecoveredActualWeakPipelineData.jsonData 11607
      [arg0]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredActualWeakPipelineData.jsonData 11607 :=
    @(recovered_closed_expr%
      DaggerRecoveredActualWeakPipelineData.jsonData 11612)
  exact @f arg0

theorem DaggerActualWeakAccessibility.wgGenerator_small.{u} :
  recovered_closed_expr%
    DaggerRecoveredActualWeakPipelineData.jsonData 11622 :=
  @(recovered_closed_expr%
    DaggerRecoveredActualWeakPipelineData.jsonData 11628)
attribute [instance] DaggerActualWeakAccessibility.wgGenerator_small

theorem DaggerActualWeakAccessibility.wgRank_regular.{u} :
  recovered_closed_expr%
    DaggerRecoveredActualWeakPipelineData.jsonData 11928 :=
  @(recovered_closed_expr%
    DaggerRecoveredActualWeakPipelineData.jsonData 11933)
attribute [instance] DaggerActualWeakAccessibility.wgRank_regular

theorem DaggerActualWeakAccessibility.wd_exists_presentation.{u} :
  recovered_closed_expr%
    DaggerRecoveredActualWeakPipelineData.jsonData 12081 :=
  @(recovered_closed_expr%
    DaggerRecoveredActualWeakPipelineData.jsonData 12097)

theorem DaggerActualWeakAccessibility.standard_wd_accessibility.{u} :
  recovered_closed_expr%
    DaggerRecoveredActualWeakPipelineData.jsonData 12137 :=
  @(recovered_closed_expr%
    DaggerRecoveredActualWeakPipelineData.jsonData 12139)

theorem DaggerActualWeakAccessibility.wdGenerator_small.{u} :
  recovered_closed_expr%
    DaggerRecoveredActualWeakPipelineData.jsonData 12147 :=
  @(recovered_closed_expr%
    DaggerRecoveredActualWeakPipelineData.jsonData 12152)
attribute [instance] DaggerActualWeakAccessibility.wdGenerator_small

theorem DaggerActualWeakAccessibility.standard_wg_accessibility.{u} :
  recovered_closed_expr%
    DaggerRecoveredActualWeakPipelineData.jsonData 12192 :=
  @(recovered_closed_expr%
    DaggerRecoveredActualWeakPipelineData.jsonData 12193)

theorem DaggerActualWeakAccessibility.wg_exists_presentation.{u} :
  recovered_closed_expr%
    DaggerRecoveredActualWeakPipelineData.jsonData 12573 :=
  @(recovered_closed_expr%
    DaggerRecoveredActualWeakPipelineData.jsonData 12593)

theorem DaggerActualWeakAccessibility.wgInclusion_cardinalAccessible.{u} :
  recovered_closed_expr%
    DaggerRecoveredActualWeakPipelineData.jsonData 12734 :=
  @(recovered_closed_expr%
    DaggerRecoveredActualWeakPipelineData.jsonData 12740)
attribute [instance] DaggerActualWeakAccessibility.wgInclusion_cardinalAccessible

theorem DaggerActualWeakAccessibility.wdInclusion_cardinalAccessible.{u} :
  recovered_closed_expr%
    DaggerRecoveredActualWeakPipelineData.jsonData 12750 :=
  @(recovered_closed_expr%
    DaggerRecoveredActualWeakPipelineData.jsonData 12755)
attribute [instance] DaggerActualWeakAccessibility.wdInclusion_cardinalAccessible

theorem DaggerActualWeakAccessibility.wg_generator_presentable.{u} :
  recovered_closed_expr%
    DaggerRecoveredActualWeakPipelineData.jsonData 12768 :=
  @(recovered_closed_expr%
    DaggerRecoveredActualWeakPipelineData.jsonData 12785)

theorem DaggerActualWeakAccessibility.wd_inclusion_accessible.{u} :
  recovered_closed_expr%
    DaggerRecoveredActualWeakPipelineData.jsonData 13285 :=
  @(recovered_closed_expr%
    DaggerRecoveredActualWeakPipelineData.jsonData 13598)

theorem DaggerActualWeakAccessibility.wd_category_accessible.{u} :
  recovered_closed_expr%
    DaggerRecoveredActualWeakPipelineData.jsonData 13605 :=
  @(recovered_closed_expr%
    DaggerRecoveredActualWeakPipelineData.jsonData 13675)

