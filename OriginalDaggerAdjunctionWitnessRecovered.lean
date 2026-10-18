import OriginalActualDaggerFreeComparisonRecovered
import OriginalRecoveredClosedExpressionApplication
import OriginalRecoveredAdjunctionWitnessData

/-! Original DaggerModels.DaggerAdjunctionWitness, with unchanged closed types and values. -/

set_option autoImplicit false
set_option maxRecDepth 100000

structure DaggerModels.OrdinaryRigidification.DaggerLiftWitness.{u}
    :
      recovered_closed_result_type%
        DaggerRecoveredAdjunctionWitnessData.jsonData 8494
        [] where
  freeSSet :
    recovered_closed_binder_type%
      DaggerRecoveredAdjunctionWitnessData.jsonData 11563
      []
  freeSSetAdjunction :
    recovered_closed_binder_type%
      DaggerRecoveredAdjunctionWitnessData.jsonData 11563
      [freeSSet]
  freeSCat :
    recovered_closed_binder_type%
      DaggerRecoveredAdjunctionWitnessData.jsonData 11563
      [freeSSet, freeSSetAdjunction]
  freeSCatAdjunction :
    recovered_closed_binder_type%
      DaggerRecoveredAdjunctionWitnessData.jsonData 11563
      [freeSSet, freeSSetAdjunction, freeSCat]
  freeSCat_objects :
    recovered_closed_binder_type%
      DaggerRecoveredAdjunctionWitnessData.jsonData 11563
      [freeSSet, freeSSetAdjunction, freeSCat, freeSCatAdjunction]
  freeSCat_unit_objects :
    recovered_closed_binder_type%
      DaggerRecoveredAdjunctionWitnessData.jsonData 11563
      [freeSSet, freeSSetAdjunction, freeSCat, freeSCatAdjunction, freeSCat_objects]
  left :
    recovered_closed_binder_type%
      DaggerRecoveredAdjunctionWitnessData.jsonData 11563
      [freeSSet, freeSSetAdjunction, freeSCat, freeSCatAdjunction, freeSCat_objects,
       freeSCat_unit_objects]
  right :
    recovered_closed_binder_type%
      DaggerRecoveredAdjunctionWitnessData.jsonData 11563
      [freeSSet, freeSSetAdjunction, freeSCat, freeSCatAdjunction, freeSCat_objects,
       freeSCat_unit_objects, left]
  adjunction :
    recovered_closed_binder_type%
      DaggerRecoveredAdjunctionWitnessData.jsonData 11563
      [freeSSet, freeSSetAdjunction, freeSCat, freeSCatAdjunction, freeSCat_objects,
       freeSCat_unit_objects, left, right]
  left_forget :
    recovered_closed_binder_type%
      DaggerRecoveredAdjunctionWitnessData.jsonData 11563
      [freeSSet, freeSSetAdjunction, freeSCat, freeSCatAdjunction, freeSCat_objects,
       freeSCat_unit_objects, left, right, adjunction]
  right_forget :
    recovered_closed_binder_type%
      DaggerRecoveredAdjunctionWitnessData.jsonData 11563
      [freeSSet, freeSSetAdjunction, freeSCat, freeSCatAdjunction, freeSCat_objects,
       freeSCat_unit_objects, left, right, adjunction, left_forget]
  homEquiv_compatibility :
    recovered_closed_binder_type%
      DaggerRecoveredAdjunctionWitnessData.jsonData 11563
      [freeSSet, freeSSetAdjunction, freeSCat, freeSCatAdjunction, freeSCat_objects,
       freeSCat_unit_objects, left, right, adjunction, left_forget, right_forget]
  homEquiv_symm_compatibility :
    recovered_closed_binder_type%
      DaggerRecoveredAdjunctionWitnessData.jsonData 11563
      [freeSSet, freeSSetAdjunction, freeSCat, freeSCatAdjunction, freeSCat_objects,
       freeSCat_unit_objects, left, right, adjunction, left_forget, right_forget,
       homEquiv_compatibility]
  unit_compatibility :
    recovered_closed_binder_type%
      DaggerRecoveredAdjunctionWitnessData.jsonData 11563
      [freeSSet, freeSSetAdjunction, freeSCat, freeSCatAdjunction, freeSCat_objects,
       freeSCat_unit_objects, left, right, adjunction, left_forget, right_forget,
       homEquiv_compatibility, homEquiv_symm_compatibility]
  counit_compatibility :
    recovered_closed_binder_type%
      DaggerRecoveredAdjunctionWitnessData.jsonData 11563
      [freeSSet, freeSSetAdjunction, freeSCat, freeSCatAdjunction, freeSCat_objects,
       freeSCat_unit_objects, left, right, adjunction, left_forget, right_forget,
       homEquiv_compatibility, homEquiv_symm_compatibility, unit_compatibility]
  comparison :
    recovered_closed_binder_type%
      DaggerRecoveredAdjunctionWitnessData.jsonData 11563
      [freeSSet, freeSSetAdjunction, freeSCat, freeSCatAdjunction, freeSCat_objects,
       freeSCat_unit_objects, left, right, adjunction, left_forget, right_forget,
       homEquiv_compatibility, homEquiv_symm_compatibility, unit_compatibility,
       counit_compatibility]
  comparison_canonical :
    recovered_closed_binder_type%
      DaggerRecoveredAdjunctionWitnessData.jsonData 11563
      [freeSSet, freeSSetAdjunction, freeSCat, freeSCatAdjunction, freeSCat_objects,
       freeSCat_unit_objects, left, right, adjunction, left_forget, right_forget,
       homEquiv_compatibility, homEquiv_symm_compatibility, unit_compatibility,
       counit_compatibility, comparison]
  comparison_unit :
    recovered_closed_binder_type%
      DaggerRecoveredAdjunctionWitnessData.jsonData 11563
      [freeSSet, freeSSetAdjunction, freeSCat, freeSCatAdjunction, freeSCat_objects,
       freeSCat_unit_objects, left, right, adjunction, left_forget, right_forget,
       homEquiv_compatibility, homEquiv_symm_compatibility, unit_compatibility,
       counit_compatibility, comparison, comparison_canonical]
  comparison_counit :
    recovered_closed_binder_type%
      DaggerRecoveredAdjunctionWitnessData.jsonData 11563
      [freeSSet, freeSSetAdjunction, freeSCat, freeSCatAdjunction, freeSCat_objects,
       freeSCat_unit_objects, left, right, adjunction, left_forget, right_forget,
       homEquiv_compatibility, homEquiv_symm_compatibility, unit_compatibility,
       counit_compatibility, comparison, comparison_canonical, comparison_unit]

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent
        `DaggerModels.OrdinaryRigidification.DaggerLiftWitness)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent
        `DaggerModels.OrdinaryRigidification.DaggerLiftWitness._sizeOf_1)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent
        `DaggerModels.OrdinaryRigidification.DaggerLiftWitness._sizeOf_inst)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent
        `DaggerModels.OrdinaryRigidification.DaggerLiftWitness.adjunction)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent
        `DaggerModels.OrdinaryRigidification.DaggerLiftWitness.casesOn)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent
        `DaggerModels.OrdinaryRigidification.DaggerLiftWitness.comparison)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent
        `DaggerModels.OrdinaryRigidification.DaggerLiftWitness.comparison_canonical)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent
        `DaggerModels.OrdinaryRigidification.DaggerLiftWitness.comparison_counit)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent
        `DaggerModels.OrdinaryRigidification.DaggerLiftWitness.comparison_unit)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent
        `DaggerModels.OrdinaryRigidification.DaggerLiftWitness.counit_compatibility)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent
        `DaggerModels.OrdinaryRigidification.DaggerLiftWitness.ctorIdx)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent
        `DaggerModels.OrdinaryRigidification.DaggerLiftWitness.freeSCat)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent
        `DaggerModels.OrdinaryRigidification.DaggerLiftWitness.freeSCatAdjunction)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent
        `DaggerModels.OrdinaryRigidification.DaggerLiftWitness.freeSCat_objects)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent
        `DaggerModels.OrdinaryRigidification.DaggerLiftWitness.freeSCat_unit_objects)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent
        `DaggerModels.OrdinaryRigidification.DaggerLiftWitness.freeSSet)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent
        `DaggerModels.OrdinaryRigidification.DaggerLiftWitness.freeSSetAdjunction)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent
        `DaggerModels.OrdinaryRigidification.DaggerLiftWitness.homEquiv_compatibility)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent
        `DaggerModels.OrdinaryRigidification.DaggerLiftWitness.homEquiv_symm_compatibility)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent
        `DaggerModels.OrdinaryRigidification.DaggerLiftWitness.left)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent
        `DaggerModels.OrdinaryRigidification.DaggerLiftWitness.left_forget)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent
        `DaggerModels.OrdinaryRigidification.DaggerLiftWitness.mk)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent
        `DaggerModels.OrdinaryRigidification.DaggerLiftWitness.mk._flat_ctor)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent
        `DaggerModels.OrdinaryRigidification.DaggerLiftWitness.mk.inj)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent
        `DaggerModels.OrdinaryRigidification.DaggerLiftWitness.mk.injEq)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent
        `DaggerModels.OrdinaryRigidification.DaggerLiftWitness.mk.noConfusion)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent
        `DaggerModels.OrdinaryRigidification.DaggerLiftWitness.mk.sizeOf_spec)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent
        `DaggerModels.OrdinaryRigidification.DaggerLiftWitness.noConfusion)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent
        `DaggerModels.OrdinaryRigidification.DaggerLiftWitness.noConfusionType)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent
        `DaggerModels.OrdinaryRigidification.DaggerLiftWitness.rec)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent
        `DaggerModels.OrdinaryRigidification.DaggerLiftWitness.recOn)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent
        `DaggerModels.OrdinaryRigidification.DaggerLiftWitness.right)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent
        `DaggerModels.OrdinaryRigidification.DaggerLiftWitness.right_forget)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent
        `DaggerModels.OrdinaryRigidification.DaggerLiftWitness.unit_compatibility)
  pure ()

theorem DaggerModels.OrdinaryRigidification.daggerRigidificationLiftWitness._proof_1.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredAdjunctionWitnessData.jsonData 99 :=
  @(recovered_closed_expr%
    DaggerRecoveredAdjunctionWitnessData.jsonData 163)

theorem DaggerModels.OrdinaryRigidification.daggerRigidificationLiftWitness._proof_2.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredAdjunctionWitnessData.jsonData 581 :=
  @(recovered_closed_expr%
    DaggerRecoveredAdjunctionWitnessData.jsonData 423)

theorem DaggerModels.OrdinaryRigidification.daggerRigidificationLiftWitness._proof_3.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredAdjunctionWitnessData.jsonData 584 :=
  @(recovered_closed_expr%
    DaggerRecoveredAdjunctionWitnessData.jsonData 433)

theorem DaggerModels.OrdinaryRigidification.daggerRigidificationLiftWitness._proof_4.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredAdjunctionWitnessData.jsonData 420 :=
  @(recovered_closed_expr%
    DaggerRecoveredAdjunctionWitnessData.jsonData 577)

theorem DaggerModels.exists_ordinaryFreeDaggerAdjunction.{u} :
  recovered_closed_expr%
    DaggerRecoveredAdjunctionWitnessData.jsonData 1678 :=
  @(recovered_closed_expr%
    DaggerRecoveredAdjunctionWitnessData.jsonData 1785)

theorem DaggerModels.OrdinaryRigidification.daggerRigidificationLiftWitness._proof_10.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredAdjunctionWitnessData.jsonData 1923 :=
  @(recovered_closed_expr%
    DaggerRecoveredAdjunctionWitnessData.jsonData 1935)

theorem DaggerModels.OrdinaryRigidification.daggerRigidificationLiftWitness._proof_8.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredAdjunctionWitnessData.jsonData 1950 :=
  @(recovered_closed_expr%
    DaggerRecoveredAdjunctionWitnessData.jsonData 1952)

theorem DaggerModels.OrdinaryRigidification.daggerRigidificationLiftWitness._proof_9.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredAdjunctionWitnessData.jsonData 2016 :=
  @(recovered_closed_expr%
    DaggerRecoveredAdjunctionWitnessData.jsonData 2029)

theorem DaggerModels.OrdinaryRigidification.daggerRigidificationLiftWitness._proof_6.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredAdjunctionWitnessData.jsonData 2766 :=
  @(recovered_closed_expr%
    DaggerRecoveredAdjunctionWitnessData.jsonData 2781)

theorem DaggerModels.OrdinaryRigidification.daggerRigidificationLiftWitness._proof_5.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredAdjunctionWitnessData.jsonData 11795 :=
  @(recovered_closed_expr%
    DaggerRecoveredAdjunctionWitnessData.jsonData 11906)

theorem DaggerModels.OrdinaryRigidification.daggerRigidificationLiftWitness._proof_7.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredAdjunctionWitnessData.jsonData 11359 :=
  @(recovered_closed_expr%
    DaggerRecoveredAdjunctionWitnessData.jsonData 11488)

noncomputable def DaggerModels.OrdinaryRigidification.daggerRigidificationLiftWitness.{u}
    :
    recovered_closed_result_type%
      DaggerRecoveredAdjunctionWitnessData.jsonData 0
      []
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredAdjunctionWitnessData.jsonData 0 :=
    @(recovered_closed_expr%
      DaggerRecoveredAdjunctionWitnessData.jsonData 3225)
  exact @f

theorem DaggerModels.OrdinaryRigidification.exists_daggerRigidificationLift.{u} :
  recovered_closed_expr%
    DaggerRecoveredAdjunctionWitnessData.jsonData 3370 :=
  @(recovered_closed_expr%
    DaggerRecoveredAdjunctionWitnessData.jsonData 3374)

