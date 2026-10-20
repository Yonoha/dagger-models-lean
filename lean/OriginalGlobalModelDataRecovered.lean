import OriginalGlobalModelRecovered
import OriginalRecoveredClosedExpressionApplication
import OriginalRecoveredGlobalModelConstructionData

/-! Original GlobalModelData, with unchanged closed types and values. -/

set_option autoImplicit false
set_option maxRecDepth 100000

noncomputable def DaggerGlobalModel.instCategoryWithCofibrationsG_globalModelData.{u}
    :
    recovered_closed_result_type%
      DaggerRecoveredGlobalModelConstructionData.jsonData 6914
      []
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredGlobalModelConstructionData.jsonData 6914 :=
    @(recovered_closed_expr%
      DaggerRecoveredGlobalModelConstructionData.jsonData 6935)
  exact @f

noncomputable def DaggerGlobalModel.instCategoryWithFibrationsG_globalModelData.{u}
    :
    recovered_closed_result_type%
      DaggerRecoveredGlobalModelConstructionData.jsonData 7385
      []
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredGlobalModelConstructionData.jsonData 7385 :=
    @(recovered_closed_expr%
      DaggerRecoveredGlobalModelConstructionData.jsonData 7493)
  exact @f

noncomputable def DaggerGlobalModel.originalIFactorization.{u}
    :
    recovered_closed_result_type%
      DaggerRecoveredGlobalModelConstructionData.jsonData 9031
      []
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredGlobalModelConstructionData.jsonData 9031 :=
    @(recovered_closed_expr%
      DaggerRecoveredGlobalModelConstructionData.jsonData 9032)
  exact @f

theorem DaggerGlobalModel.cofibrationFactorization._proof_1.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredGlobalModelConstructionData.jsonData 10800 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalModelConstructionData.jsonData 10807)

theorem DaggerGlobalModel.cofibrationFactorization._proof_2.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredGlobalModelConstructionData.jsonData 10437 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalModelConstructionData.jsonData 10446)

noncomputable def DaggerGlobalModel.cofibrationFactorization.{u}
    (arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalModelConstructionData.jsonData 10489
        [])
    :
    recovered_closed_result_type%
      DaggerRecoveredGlobalModelConstructionData.jsonData 10489
      [arg0]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredGlobalModelConstructionData.jsonData 10489 :=
    @(recovered_closed_expr%
      DaggerRecoveredGlobalModelConstructionData.jsonData 10500)
  exact @f arg0

noncomputable def DaggerGlobalModel.cofibrationMapFactorization.{u}
    (arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalModelConstructionData.jsonData 9044
        [])
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalModelConstructionData.jsonData 9044
        [arg0]}
    {arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalModelConstructionData.jsonData 9044
        [arg0, arg1]}
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalModelConstructionData.jsonData 9044
        [arg0, arg1, arg2])
    :
    recovered_closed_result_type%
      DaggerRecoveredGlobalModelConstructionData.jsonData 9044
      [arg0, arg1, arg2, arg3]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredGlobalModelConstructionData.jsonData 9044 :=
    @(recovered_closed_expr%
      DaggerRecoveredGlobalModelConstructionData.jsonData 9058)
  exact @f arg0 arg1 arg2 arg3

theorem DaggerGlobalModel.originalIMap_Z.{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalModelConstructionData.jsonData 7956 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalModelConstructionData.jsonData 7962)

structure DaggerGlobalModel.CombinatorialData.{u, u_1, u_2, u_3, u_4, u_5}
    (arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalModelConstructionData.jsonData 8914
        [])
    :
      recovered_closed_result_type%
        DaggerRecoveredGlobalModelConstructionData.jsonData 8914
        [arg0] where
  model :
    recovered_closed_binder_type%
      DaggerRecoveredGlobalModelConstructionData.jsonData 8144
      [arg0]
  weakStructure :
    recovered_closed_binder_type%
      DaggerRecoveredGlobalModelConstructionData.jsonData 8144
      [arg0, model]
  fibrationStructure :
    recovered_closed_binder_type%
      DaggerRecoveredGlobalModelConstructionData.jsonData 8144
      [arg0, model, weakStructure]
  cofibrationStructure :
    recovered_closed_binder_type%
      DaggerRecoveredGlobalModelConstructionData.jsonData 8144
      [arg0, model, weakStructure, fibrationStructure]
  locallyFinitelyPresentable :
    recovered_closed_binder_type%
      DaggerRecoveredGlobalModelConstructionData.jsonData 8144
      [arg0, model, weakStructure, fibrationStructure, cofibrationStructure]
  smallI :
    recovered_closed_binder_type%
      DaggerRecoveredGlobalModelConstructionData.jsonData 8144
      [arg0, model, weakStructure, fibrationStructure, cofibrationStructure,
       locallyFinitelyPresentable]
  smallJ :
    recovered_closed_binder_type%
      DaggerRecoveredGlobalModelConstructionData.jsonData 8144
      [arg0, model, weakStructure, fibrationStructure, cofibrationStructure,
       locallyFinitelyPresentable, smallI]
  domainsI :
    recovered_closed_binder_type%
      DaggerRecoveredGlobalModelConstructionData.jsonData 8144
      [arg0, model, weakStructure, fibrationStructure, cofibrationStructure,
       locallyFinitelyPresentable, smallI, smallJ]
  domainsJ :
    recovered_closed_binder_type%
      DaggerRecoveredGlobalModelConstructionData.jsonData 8144
      [arg0, model, weakStructure, fibrationStructure, cofibrationStructure,
       locallyFinitelyPresentable, smallI, smallJ, domainsI]
  weak :
    recovered_closed_binder_type%
      DaggerRecoveredGlobalModelConstructionData.jsonData 8144
      [arg0, model, weakStructure, fibrationStructure, cofibrationStructure,
       locallyFinitelyPresentable, smallI, smallJ, domainsI, domainsJ]
  fibrations :
    recovered_closed_binder_type%
      DaggerRecoveredGlobalModelConstructionData.jsonData 8144
      [arg0, model, weakStructure, fibrationStructure, cofibrationStructure,
       locallyFinitelyPresentable, smallI, smallJ, domainsI, domainsJ, weak]
  cofibrations :
    recovered_closed_binder_type%
      DaggerRecoveredGlobalModelConstructionData.jsonData 8144
      [arg0, model, weakStructure, fibrationStructure, cofibrationStructure,
       locallyFinitelyPresentable, smallI, smallJ, domainsI, domainsJ, weak, fibrations]
  trivialFibrations :
    recovered_closed_binder_type%
      DaggerRecoveredGlobalModelConstructionData.jsonData 8144
      [arg0, model, weakStructure, fibrationStructure, cofibrationStructure,
       locallyFinitelyPresentable, smallI, smallJ, domainsI, domainsJ, weak, fibrations,
       cofibrations]
  trivialCofibrations :
    recovered_closed_binder_type%
      DaggerRecoveredGlobalModelConstructionData.jsonData 8144
      [arg0, model, weakStructure, fibrationStructure, cofibrationStructure,
       locallyFinitelyPresentable, smallI, smallJ, domainsI, domainsJ, weak, fibrations,
       cofibrations, trivialFibrations]
  cofibrationFactorization :
    recovered_closed_binder_type%
      DaggerRecoveredGlobalModelConstructionData.jsonData 8144
      [arg0, model, weakStructure, fibrationStructure, cofibrationStructure,
       locallyFinitelyPresentable, smallI, smallJ, domainsI, domainsJ, weak, fibrations,
       cofibrations, trivialFibrations, trivialCofibrations]
  trivialCofibrationFactorization :
    recovered_closed_binder_type%
      DaggerRecoveredGlobalModelConstructionData.jsonData 8144
      [arg0, model, weakStructure, fibrationStructure, cofibrationStructure,
       locallyFinitelyPresentable, smallI, smallJ, domainsI, domainsJ, weak, fibrations,
       cofibrations, trivialFibrations, trivialCofibrations, cofibrationFactorization]

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerGlobalModel.CombinatorialData)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerGlobalModel.CombinatorialData._sizeOf_1)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerGlobalModel.CombinatorialData._sizeOf_inst)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerGlobalModel.CombinatorialData.casesOn)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerGlobalModel.CombinatorialData.cofibrationFactorization)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerGlobalModel.CombinatorialData.cofibrationStructure)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerGlobalModel.CombinatorialData.cofibrations)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerGlobalModel.CombinatorialData.ctorIdx)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerGlobalModel.CombinatorialData.domainsI)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerGlobalModel.CombinatorialData.domainsJ)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerGlobalModel.CombinatorialData.fibrationStructure)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerGlobalModel.CombinatorialData.fibrations)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerGlobalModel.CombinatorialData.locallyFinitelyPresentable)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerGlobalModel.CombinatorialData.mk)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerGlobalModel.CombinatorialData.mk._flat_ctor)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerGlobalModel.CombinatorialData.mk.inj)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerGlobalModel.CombinatorialData.mk.injEq)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerGlobalModel.CombinatorialData.mk.noConfusion)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerGlobalModel.CombinatorialData.mk.sizeOf_spec)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerGlobalModel.CombinatorialData.model)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerGlobalModel.CombinatorialData.noConfusion)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerGlobalModel.CombinatorialData.noConfusionType)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerGlobalModel.CombinatorialData.rec)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerGlobalModel.CombinatorialData.recOn)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerGlobalModel.CombinatorialData.smallI)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerGlobalModel.CombinatorialData.smallJ)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerGlobalModel.CombinatorialData.trivialCofibrationFactorization)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerGlobalModel.CombinatorialData.trivialCofibrations)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerGlobalModel.CombinatorialData.trivialFibrations)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerGlobalModel.CombinatorialData.weak)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerGlobalModel.CombinatorialData.weakStructure)
  pure ()

theorem DaggerGlobalModel.originalJFactorization._proof_1.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredGlobalModelConstructionData.jsonData 8167 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalModelConstructionData.jsonData 8203)

noncomputable def DaggerGlobalModel.originalJFactorization.{u}
    (arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalModelConstructionData.jsonData 8208
        [])
    :
    recovered_closed_result_type%
      DaggerRecoveredGlobalModelConstructionData.jsonData 8208
      [arg0]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredGlobalModelConstructionData.jsonData 8208 :=
    @(recovered_closed_expr%
      DaggerRecoveredGlobalModelConstructionData.jsonData 8217)
  exact @f arg0

theorem DaggerGlobalModel.trivialCofibrationFactorization._proof_1.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredGlobalModelConstructionData.jsonData 10358 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalModelConstructionData.jsonData 10367)

theorem DaggerGlobalModel.trivialCofibrationFactorization._proof_2.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredGlobalModelConstructionData.jsonData 8420 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalModelConstructionData.jsonData 8432)

noncomputable def DaggerGlobalModel.trivialCofibrationFactorization.{u}
    (arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalModelConstructionData.jsonData 8970
        [])
    :
    recovered_closed_result_type%
      DaggerRecoveredGlobalModelConstructionData.jsonData 8970
      [arg0]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredGlobalModelConstructionData.jsonData 8970 :=
    @(recovered_closed_expr%
      DaggerRecoveredGlobalModelConstructionData.jsonData 8984)
  exact @f arg0

noncomputable def DaggerGlobalModel.combinatorialData.{u}
    (arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalModelConstructionData.jsonData 10509
        [])
    :
    recovered_closed_result_type%
      DaggerRecoveredGlobalModelConstructionData.jsonData 10509
      [arg0]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredGlobalModelConstructionData.jsonData 10509 :=
    @(recovered_closed_expr%
      DaggerRecoveredGlobalModelConstructionData.jsonData 10550)
  exact @f arg0

noncomputable def DaggerGlobalModel.standardCombinatorialData.{u}
    :
    recovered_closed_result_type%
      DaggerRecoveredGlobalModelConstructionData.jsonData 7987
      []
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredGlobalModelConstructionData.jsonData 7987 :=
    @(recovered_closed_expr%
      DaggerRecoveredGlobalModelConstructionData.jsonData 7989)
  exact @f

theorem DaggerGlobalModel.originalIMap_i.{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalModelConstructionData.jsonData 8243 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalModelConstructionData.jsonData 8249)

noncomputable def DaggerGlobalModel.standardFibrations.{u}
    :
    recovered_closed_result_type%
      DaggerRecoveredGlobalModelConstructionData.jsonData 7385
      []
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredGlobalModelConstructionData.jsonData 7385 :=
    @(recovered_closed_expr%
      DaggerRecoveredGlobalModelConstructionData.jsonData 7493)
  exact @f

theorem DaggerGlobalModel.trivialCofibrationFactorization_Z.{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalModelConstructionData.jsonData 8288 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalModelConstructionData.jsonData 8291)

theorem DaggerGlobalModel.originalIMap_p.{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalModelConstructionData.jsonData 8317 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalModelConstructionData.jsonData 8323)

noncomputable def DaggerGlobalModel.standardModelCategory.{u}
    :
    recovered_closed_result_type%
      DaggerRecoveredGlobalModelConstructionData.jsonData 7855
      []
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredGlobalModelConstructionData.jsonData 7855 :=
    @(recovered_closed_expr%
      DaggerRecoveredGlobalModelConstructionData.jsonData 8331)
  exact @f

theorem DaggerGlobalModel.cofibrationFactorization_i.{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalModelConstructionData.jsonData 8382 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalModelConstructionData.jsonData 8385)

theorem DaggerGlobalModel.trivialCofibrationFactorization_i.{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalModelConstructionData.jsonData 8396 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalModelConstructionData.jsonData 8399)

theorem DaggerGlobalModel.cofibrationFactorization_Z.{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalModelConstructionData.jsonData 8911 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalModelConstructionData.jsonData 8913)

noncomputable def DaggerGlobalModel.trivialCofibrationMapFactorization.{u}
    (arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalModelConstructionData.jsonData 9281
        [])
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalModelConstructionData.jsonData 9281
        [arg0]}
    {arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalModelConstructionData.jsonData 9281
        [arg0, arg1]}
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalModelConstructionData.jsonData 9281
        [arg0, arg1, arg2])
    :
    recovered_closed_result_type%
      DaggerRecoveredGlobalModelConstructionData.jsonData 9281
      [arg0, arg1, arg2, arg3]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredGlobalModelConstructionData.jsonData 9281 :=
    @(recovered_closed_expr%
      DaggerRecoveredGlobalModelConstructionData.jsonData 9292)
  exact @f arg0 arg1 arg2 arg3

noncomputable def DaggerGlobalModel.standardWeakEquivalences.{u}
    :
    recovered_closed_result_type%
      DaggerRecoveredGlobalModelConstructionData.jsonData 7641
      []
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredGlobalModelConstructionData.jsonData 7641 :=
    @(recovered_closed_expr%
      DaggerRecoveredGlobalModelConstructionData.jsonData 10722)
  exact @f

theorem DaggerGlobalModel.trivialCofibrationFactorization_p.{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalModelConstructionData.jsonData 10742 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalModelConstructionData.jsonData 10745)

theorem DaggerGlobalModel.cofibrationFactorization_p.{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalModelConstructionData.jsonData 10757 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalModelConstructionData.jsonData 10760)

noncomputable def DaggerGlobalModel.standardCofibrations.{u}
    :
    recovered_closed_result_type%
      DaggerRecoveredGlobalModelConstructionData.jsonData 6914
      []
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredGlobalModelConstructionData.jsonData 6914 :=
    @(recovered_closed_expr%
      DaggerRecoveredGlobalModelConstructionData.jsonData 6935)
  exact @f

