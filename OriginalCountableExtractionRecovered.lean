import OriginalCountableExtractionOuterRecovered
import OriginalRecoveredClosedExpressionApplication
import OriginalRecoveredCountableExtractionRealizationData

/-! Original CountableExtraction, with unchanged closed types and values. -/

set_option autoImplicit false
set_option maxRecDepth 100000

theorem DaggerCountableExtraction.extractedInterval._proof_1.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 47825 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 47844)

noncomputable def DaggerCountableExtraction.extractedInterval.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 43915
        []}
    (arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 43915
        [arg0])
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 43915
        [arg0, arg1])
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 43915
        [arg0, arg1, arg2])
    :
    recovered_closed_result_type%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 43915
      [arg0, arg1, arg2, arg3]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 43915 :=
    @(recovered_closed_expr%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 43948)
  exact @f arg0 arg1 arg2 arg3

structure DaggerCountableExtraction.ExtractionData.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 48658
        []}
    (arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 48658
        [arg0])
    :
      recovered_closed_result_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 48658
        [arg0, arg1] where
  nonemptyG :
    recovered_closed_binder_type%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 44979
      [arg0, arg1]
  geometricG :
    recovered_closed_binder_type%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 44979
      [arg0, arg1, nonemptyG]
  interval :
    recovered_closed_binder_type%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 44979
      [arg0, arg1, nonemptyG, geometricG]
  interval_eq :
    recovered_closed_binder_type%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 44979
      [arg0, arg1, nonemptyG, geometricG, interval]
  psi :
    recovered_closed_binder_type%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 44979
      [arg0, arg1, nonemptyG, geometricG, interval, interval_eq]
  psi_eq :
    recovered_closed_binder_type%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 44979
      [arg0, arg1, nonemptyG, geometricG, interval, interval_eq, psi]
  fac :
    recovered_closed_binder_type%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 44979
      [arg0, arg1, nonemptyG, geometricG, interval, interval_eq, psi, psi_eq]

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerCountableExtraction.ExtractionData)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerCountableExtraction.ExtractionData._sizeOf_1)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerCountableExtraction.ExtractionData._sizeOf_inst)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerCountableExtraction.ExtractionData.casesOn)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerCountableExtraction.ExtractionData.ctorIdx)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerCountableExtraction.ExtractionData.fac)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerCountableExtraction.ExtractionData.geometricG)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerCountableExtraction.ExtractionData.interval)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerCountableExtraction.ExtractionData.interval_eq)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerCountableExtraction.ExtractionData.mk)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerCountableExtraction.ExtractionData.mk._flat_ctor)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerCountableExtraction.ExtractionData.mk.inj)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerCountableExtraction.ExtractionData.mk.injEq)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerCountableExtraction.ExtractionData.mk.noConfusion)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerCountableExtraction.ExtractionData.mk.sizeOf_spec)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerCountableExtraction.ExtractionData.noConfusion)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerCountableExtraction.ExtractionData.noConfusionType)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerCountableExtraction.ExtractionData.nonemptyG)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerCountableExtraction.ExtractionData.psi)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerCountableExtraction.ExtractionData.psi_eq)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerCountableExtraction.ExtractionData.rec)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerCountableExtraction.ExtractionData.recOn)
  pure ()

noncomputable def DaggerCountableExtraction.ExtractionData.stage.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 49268
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 49268
        [arg0]}
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 49268
        [arg0, arg1])
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 49268
        [arg0, arg1, arg2])
    :
    recovered_closed_result_type%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 49268
      [arg0, arg1, arg2, arg3]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 49268 :=
    @(recovered_closed_expr%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 49277)
  exact @f arg0 arg1 arg2 arg3

theorem DaggerCountableExtraction.ExtractionData.innerState._proof_1.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 49288 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 49293)

noncomputable def DaggerCountableExtraction.ExtractionData.innerState.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 43775
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 43775
        [arg0]}
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 43775
        [arg0, arg1])
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 43775
        [arg0, arg1, arg2])
    (arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 43775
        [arg0, arg1, arg2, arg3])
    :
    recovered_closed_result_type%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 43775
      [arg0, arg1, arg2, arg3, arg4]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 43775 :=
    @(recovered_closed_expr%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 43798)
  exact @f arg0 arg1 arg2 arg3 arg4

noncomputable def DaggerCountableExtraction.ExtractionData.ordinaryAt.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 43453
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 43453
        [arg0]}
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 43453
        [arg0, arg1])
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 43453
        [arg0, arg1, arg2])
    (arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 43453
        [arg0, arg1, arg2, arg3])
    (arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 43453
        [arg0, arg1, arg2, arg3, arg4])
    :
    recovered_closed_result_type%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 43453
      [arg0, arg1, arg2, arg3, arg4, arg5]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 43453 :=
    @(recovered_closed_expr%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 43474)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5

noncomputable def DaggerCountableExtraction.ExtractionData.F.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 43641
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 43641
        [arg0]}
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 43641
        [arg0, arg1])
    :
    recovered_closed_result_type%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 43641
      [arg0, arg1, arg2]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 43641 :=
    @(recovered_closed_expr%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 43654)
  exact @f arg0 arg1 arg2

noncomputable def DaggerCountableExtraction.ExtractionData.cocone.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 49546
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 49546
        [arg0]}
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 49546
        [arg0, arg1])
    :
    recovered_closed_result_type%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 49546
      [arg0, arg1, arg2]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 49546 :=
    @(recovered_closed_expr%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 49549)
  exact @f arg0 arg1 arg2

theorem DaggerCountableExtraction.ExtractionData.intervalIso._proof_1.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 48258 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 48273)

noncomputable def DaggerCountableExtraction.ExtractionData.intervalIso.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 49637
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 49637
        [arg0]}
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 49637
        [arg0, arg1])
    :
    recovered_closed_result_type%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 49637
      [arg0, arg1, arg2]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 49637 :=
    @(recovered_closed_expr%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 49640)
  exact @f arg0 arg1 arg2

theorem DaggerCountableExtraction.ExtractionData.interval_inclusion.{u} :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 45030 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 45658)

theorem DaggerCountableExtraction.ExtractionData.interval_inclusion_assoc.{u} :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 43538 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 43638)

noncomputable def DaggerCountableExtraction.ExtractionData.wholeUP.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 45016
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 45016
        [arg0]}
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 45016
        [arg0, arg1])
    :
    recovered_closed_result_type%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 45016
      [arg0, arg1, arg2]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 45016 :=
    @(recovered_closed_expr%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 45023)
  exact @f arg0 arg1 arg2

noncomputable def DaggerCountableExtraction.ExtractionData.desc.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 48277
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 48277
        [arg0]}
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 48277
        [arg0, arg1])
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 48277
        [arg0, arg1, arg2])
    :
    recovered_closed_result_type%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 48277
      [arg0, arg1, arg2, arg3]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 48277 :=
    @(recovered_closed_expr%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 48288)
  exact @f arg0 arg1 arg2 arg3

theorem DaggerCountableExtraction.ExtractionData.desc_fac.{u} :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 44754 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 44767)

theorem DaggerCountableExtraction.ExtractionData.desc_uniq.{u} :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 43695 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 43766)

theorem DaggerCountableExtraction.ExtractionData.local_projection_fac.{u} :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 43835 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 43910)

noncomputable def DaggerCountableExtraction.ExtractionData.innerF.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 45001
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 45001
        [arg0]}
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 45001
        [arg0, arg1])
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 45001
        [arg0, arg1, arg2])
    :
    recovered_closed_result_type%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 45001
      [arg0, arg1, arg2, arg3]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 45001 :=
    @(recovered_closed_expr%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 45011)
  exact @f arg0 arg1 arg2 arg3

noncomputable def DaggerCountableExtraction.ExtractionData.innerCocone.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 47788
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 47788
        [arg0]}
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 47788
        [arg0, arg1])
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 47788
        [arg0, arg1, arg2])
    :
    recovered_closed_result_type%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 47788
      [arg0, arg1, arg2, arg3]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 47788 :=
    @(recovered_closed_expr%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 47798)
  exact @f arg0 arg1 arg2 arg3

noncomputable def DaggerCountableExtraction.ExtractionData.innerUP.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 43971
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 43971
        [arg0]}
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 43971
        [arg0, arg1])
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 43971
        [arg0, arg1, arg2])
    :
    recovered_closed_result_type%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 43971
      [arg0, arg1, arg2, arg3]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 43971 :=
    @(recovered_closed_expr%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 43999)
  exact @f arg0 arg1 arg2 arg3

noncomputable def DaggerCountableExtraction.ExtractionData.innerDesc.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 44018
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 44018
        [arg0]}
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 44018
        [arg0, arg1])
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 44018
        [arg0, arg1, arg2])
    (arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 44018
        [arg0, arg1, arg2, arg3])
    :
    recovered_closed_result_type%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 44018
      [arg0, arg1, arg2, arg3, arg4]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 44018 :=
    @(recovered_closed_expr%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 44032)
  exact @f arg0 arg1 arg2 arg3 arg4

theorem DaggerCountableExtraction.ExtractionData.sphere_nullity.{u} :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 44041 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 44470)

theorem DaggerCountableExtraction.countableExtraction._proof_1.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 49536 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 49543)

theorem DaggerCountableExtraction.countableExtraction._proof_2.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 49392 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 49415)

noncomputable def DaggerCountableExtraction.countableExtraction.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 49419
        []}
    (arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 49419
        [arg0])
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 49419
        [arg0, arg1])
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 49419
        [arg0, arg1, arg2])
    :
    recovered_closed_result_type%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 49419
      [arg0, arg1, arg2, arg3]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 49419 :=
    @(recovered_closed_expr%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 49442)
  exact @f arg0 arg1 arg2 arg3

theorem DaggerCountableExtraction.extraction.{u} :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 44493 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 44541)

theorem DaggerCountableExtraction.ExtractionData.innerDesc_fac.{u} :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 48479 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 48494)

theorem DaggerCountableExtraction.ExtractionData.innerDesc_uniq.{u} :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 44823 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 44899)

noncomputable def DaggerCountableExtraction.ExtractionData.toG.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 49599
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 49599
        [arg0]}
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 49599
        [arg0, arg1])
    :
    recovered_closed_result_type%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 49599
      [arg0, arg1, arg2]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 49599 :=
    @(recovered_closed_expr%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 49606)
  exact @f arg0 arg1 arg2

theorem DaggerCountableExtraction.ExtractionData.interval_psi.{u} :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 48296 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 48431)

theorem DaggerCountableExtraction.ExtractionData.interval_psi_assoc.{u} :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 45701 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 45798)

noncomputable def DaggerCountableExtraction.ExtractionData.outerComposition.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 47676
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 47676
        [arg0]}
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 47676
        [arg0, arg1])
    :
    recovered_closed_result_type%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 47676
      [arg0, arg1, arg2]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 47676 :=
    @(recovered_closed_expr%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 47684)
  exact @f arg0 arg1 arg2

noncomputable def DaggerCountableExtraction.ExtractionData.innerToG.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 47850
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 47850
        [arg0]}
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 47850
        [arg0, arg1])
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 47850
        [arg0, arg1, arg2])
    :
    recovered_closed_result_type%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 47850
      [arg0, arg1, arg2, arg3]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 47850 :=
    @(recovered_closed_expr%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 47860)
  exact @f arg0 arg1 arg2 arg3

theorem DaggerCountableExtraction.ExtractionData.local_fac.{u} :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 47881 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 47954)

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerCountableExtraction.extractedInterval.eq_1)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerCountableExtraction.ExtractionData.cocone.eq_1)
  pure ()

noncomputable def DaggerCountableExtraction.ExtractionData.innerStep.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 48628
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 48628
        [arg0]}
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 48628
        [arg0, arg1])
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 48628
        [arg0, arg1, arg2])
    (arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 48628
        [arg0, arg1, arg2, arg3])
    :
    recovered_closed_result_type%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 48628
      [arg0, arg1, arg2, arg3, arg4]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 48628 :=
    @(recovered_closed_expr%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 48641)
  exact @f arg0 arg1 arg2 arg3 arg4

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerCountableExtraction.outerInclusion.eq_1)
  pure ()

theorem DaggerCountableExtraction.ExtractionData.step_kills.{u} :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 48816 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 48833)

theorem DaggerCountableExtraction.ExtractionData.local_mono.{u} :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 48882 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 49249)

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerCountableExtraction.outerLeg.eq_1)
  pure ()

noncomputable def DaggerCountableExtraction.ExtractionData.finiteAt.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 49495
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 49495
        [arg0]}
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 49495
        [arg0, arg1])
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 49495
        [arg0, arg1, arg2])
    (arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 49495
        [arg0, arg1, arg2, arg3])
    (arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 49495
        [arg0, arg1, arg2, arg3, arg4])
    :
    recovered_closed_result_type%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 49495
      [arg0, arg1, arg2, arg3, arg4, arg5]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 49495 :=
    @(recovered_closed_expr%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 49508)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerCountableExtraction.ExtractionData.intervalIso.eq_1)
  pure ()

noncomputable def DaggerCountableExtraction.ExtractionData.innerComposition.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 49572
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 49572
        [arg0]}
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 49572
        [arg0, arg1])
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 49572
        [arg0, arg1, arg2])
    :
    recovered_closed_result_type%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 49572
      [arg0, arg1, arg2, arg3]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 49572 :=
    @(recovered_closed_expr%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 49583)
  exact @f arg0 arg1 arg2 arg3

theorem DaggerCountableExtraction.ExtractionData.projection_eq.{u} :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 49615 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 49621)

