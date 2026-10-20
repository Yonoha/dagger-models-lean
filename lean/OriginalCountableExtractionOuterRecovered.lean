import OriginalCountableExtractionInnerRecovered
import OriginalRecoveredClosedExpressionApplication
import OriginalRecoveredCountableExtractionRealizationData

/-! Original CountableExtractionOuter, with unchanged closed types and values. -/

set_option autoImplicit false
set_option maxRecDepth 100000

structure DaggerCountableExtraction.OuterState.{u}
    (arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 39917
        [])
    :
      recovered_closed_result_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 39917
        [arg0] where
  K :
    recovered_closed_binder_type%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 41167
      [arg0]
  phi :
    recovered_closed_binder_type%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 41167
      [arg0, K]
  countable :
    recovered_closed_binder_type%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 41167
      [arg0, K, phi]

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerCountableExtraction.OuterState)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerCountableExtraction.OuterState.K)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerCountableExtraction.OuterState._sizeOf_1)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerCountableExtraction.OuterState._sizeOf_inst)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerCountableExtraction.OuterState.casesOn)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerCountableExtraction.OuterState.countable)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerCountableExtraction.OuterState.ctorIdx)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerCountableExtraction.OuterState.mk)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerCountableExtraction.OuterState.mk._flat_ctor)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerCountableExtraction.OuterState.mk.inj)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerCountableExtraction.OuterState.mk.injEq)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerCountableExtraction.OuterState.mk.noConfusion)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerCountableExtraction.OuterState.mk.sizeOf_spec)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerCountableExtraction.OuterState.noConfusion)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerCountableExtraction.OuterState.noConfusionType)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerCountableExtraction.OuterState.phi)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerCountableExtraction.OuterState.rec)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerCountableExtraction.OuterState.recOn)
  pure ()

theorem DaggerCountableExtraction.outerState._proof_1.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 40288 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 40299)

noncomputable def DaggerCountableExtraction.outerState.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 41577
        []}
    (arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 41577
        [arg0])
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 41577
        [arg0, arg1])
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 41577
        [arg0, arg1, arg2])
    (arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 41577
        [arg0, arg1, arg2, arg3])
    :
    recovered_closed_result_type%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 41577
      [arg0, arg1, arg2, arg3, arg4]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 41577 :=
    @(recovered_closed_expr%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 41621)
  exact @f arg0 arg1 arg2 arg3 arg4

theorem DaggerCountableExtraction.outerArrow._proof_1.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 40344 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 40351)

noncomputable def DaggerCountableExtraction.outerArrow.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 40367
        []}
    (arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 40367
        [arg0])
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 40367
        [arg0, arg1])
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 40367
        [arg0, arg1, arg2])
    (arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 40367
        [arg0, arg1, arg2, arg3])
    :
    recovered_closed_result_type%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 40367
      [arg0, arg1, arg2, arg3, arg4]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 40367 :=
    @(recovered_closed_expr%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 40385)
  exact @f arg0 arg1 arg2 arg3 arg4

noncomputable def DaggerCountableExtraction.outerF.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 40534
        []}
    (arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 40534
        [arg0])
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 40534
        [arg0, arg1])
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 40534
        [arg0, arg1, arg2])
    :
    recovered_closed_result_type%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 40534
      [arg0, arg1, arg2, arg3]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 40534 :=
    @(recovered_closed_expr%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 40538)
  exact @f arg0 arg1 arg2 arg3

theorem DaggerCountableExtraction.outerCocone._proof_1.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 39565 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 39570)

noncomputable def DaggerCountableExtraction.outerCocone.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 41336
        []}
    (arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 41336
        [arg0])
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 41336
        [arg0, arg1])
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 41336
        [arg0, arg1, arg2])
    :
    recovered_closed_result_type%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 41336
      [arg0, arg1, arg2, arg3]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 41336 :=
    @(recovered_closed_expr%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 41342)
  exact @f arg0 arg1 arg2 arg3

noncomputable abbrev DaggerCountableExtraction.outerTarget.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 41145
        []}
    (arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 41145
        [arg0])
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 41145
        [arg0, arg1])
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 41145
        [arg0, arg1, arg2])
    :
    recovered_closed_result_type%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 41145
      [arg0, arg1, arg2, arg3]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 41145 :=
    @(recovered_closed_expr%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 41151)
  exact @f arg0 arg1 arg2 arg3

noncomputable def DaggerCountableExtraction.outerIsColimit.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 39923
        []}
    (arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 39923
        [arg0])
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 39923
        [arg0, arg1])
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 39923
        [arg0, arg1, arg2])
    :
    recovered_closed_result_type%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 39923
      [arg0, arg1, arg2, arg3]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 39923 :=
    @(recovered_closed_expr%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 39934)
  exact @f arg0 arg1 arg2 arg3

theorem DaggerCountableExtraction.outerToG._proof_1 :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 36262 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 36263)

theorem DaggerCountableExtraction.outerToG._proof_2.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 39680 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 39806)

noncomputable def DaggerCountableExtraction.outerToG.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 42132
        []}
    (arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 42132
        [arg0])
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 42132
        [arg0, arg1])
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 42132
        [arg0, arg1, arg2])
    :
    recovered_closed_result_type%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 42132
      [arg0, arg1, arg2, arg3]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 42132 :=
    @(recovered_closed_expr%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 42146)
  exact @f arg0 arg1 arg2 arg3

noncomputable def DaggerCountableExtraction.outerPsi.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 39586
        []}
    (arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 39586
        [arg0])
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 39586
        [arg0, arg1])
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 39586
        [arg0, arg1, arg2])
    :
    recovered_closed_result_type%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 39586
      [arg0, arg1, arg2, arg3]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 39586 :=
    @(recovered_closed_expr%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 39617)
  exact @f arg0 arg1 arg2 arg3

theorem DaggerCountableExtraction.outer_naturality.{u} :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 39844 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 39874)

noncomputable def DaggerCountableExtraction.outerDesc.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 39899
        []}
    (arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 39899
        [arg0])
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 39899
        [arg0, arg1])
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 39899
        [arg0, arg1, arg2])
    (arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 39899
        [arg0, arg1, arg2, arg3])
    :
    recovered_closed_result_type%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 39899
      [arg0, arg1, arg2, arg3, arg4]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 39899 :=
    @(recovered_closed_expr%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 39916)
  exact @f arg0 arg1 arg2 arg3 arg4

noncomputable def DaggerCountableExtraction.outerLeg.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 39943
        []}
    (arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 39943
        [arg0])
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 39943
        [arg0, arg1])
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 39943
        [arg0, arg1, arg2])
    (arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 39943
        [arg0, arg1, arg2, arg3])
    :
    recovered_closed_result_type%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 39943
      [arg0, arg1, arg2, arg3, arg4]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 39943 :=
    @(recovered_closed_expr%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 39956)
  exact @f arg0 arg1 arg2 arg3 arg4

theorem DaggerCountableExtraction.outerLeg_psi.{u} :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 41319 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 41332)

theorem DaggerCountableExtraction.outerLeg_psi_assoc.{u} :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 39995 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 40097)

theorem DaggerCountableExtraction.outer_step_kills.{u} :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 40165 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 40194)

noncomputable def DaggerCountableExtraction.outerInclusion.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 40304
        []}
    (arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 40304
        [arg0])
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 40304
        [arg0, arg1])
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 40304
        [arg0, arg1, arg2])
    :
    recovered_closed_result_type%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 40304
      [arg0, arg1, arg2, arg3]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 40304 :=
    @(recovered_closed_expr%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 40313)
  exact @f arg0 arg1 arg2 arg3

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerCountableExtraction.outerF.eq_1)
  pure ()

theorem DaggerCountableExtraction.outerInclusion_psi.{u} :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 40425 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 40434)

theorem DaggerCountableExtraction.outer_vertices.{u} :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 40820 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 41057)

theorem DaggerCountableExtraction.outer_arrow_leg.{u} :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 41356 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 41539)

theorem DaggerCountableExtraction.outer_arrow_leg_assoc.{u} :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 41222 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 41310)

noncomputable def DaggerCountableExtraction.outerComposition.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 41630
        []}
    (arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 41630
        [arg0])
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 41630
        [arg0, arg1])
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 41630
        [arg0, arg1, arg2])
    :
    recovered_closed_result_type%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 41630
      [arg0, arg1, arg2, arg3]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 41630 :=
    @(recovered_closed_expr%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 41637)
  exact @f arg0 arg1 arg2 arg3

theorem DaggerCountableExtraction.outerDesc_fac.{u} :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 41671 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 41686)

theorem DaggerCountableExtraction.outer_cof.{u} :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 41694 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 41751)

theorem DaggerCountableExtraction.outerInclusion_psi_assoc.{u} :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 41794 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 41858)

theorem DaggerCountableExtraction.outerDesc_uniq.{u} :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 41931 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 42006)

theorem DaggerCountableExtraction.outer_sphere_nullity.{u} :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 42395 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 43390)

theorem DaggerCountableExtraction.outer_geometric.{u} :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 42011 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 42109)

theorem DaggerCountableExtraction.outer_countable.{u} :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 42114 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 42125)

theorem DaggerCountableExtraction.outer_mono.{u} :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 42199 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 42389)

