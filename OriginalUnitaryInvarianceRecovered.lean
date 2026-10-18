import OriginalUnitaryWitnessHomotopyRecovered
import OriginalRecoveredClosedExpressionApplication
import OriginalRecoveredUnitaryPrivateExpression
import OriginalRecoveredUnitaryModelFoundationData

/-! Original UnitaryInvariance, with unchanged closed types and values. -/

set_option autoImplicit false
set_option maxRecDepth 100000

structure DaggerUnitaryInvariance.FunctorialFibrantReplacement.{u}
    :
      recovered_closed_result_type%
        DaggerRecoveredUnitaryModelFoundationData.jsonData 26092
        [] where
  functor :
    recovered_closed_binder_type%
      DaggerRecoveredUnitaryModelFoundationData.jsonData 85056
      []
  unit :
    recovered_closed_binder_type%
      DaggerRecoveredUnitaryModelFoundationData.jsonData 85056
      [functor]
  cofibration :
    recovered_closed_binder_type%
      DaggerRecoveredUnitaryModelFoundationData.jsonData 85056
      [functor, unit]
  weakEquivalence :
    recovered_closed_binder_type%
      DaggerRecoveredUnitaryModelFoundationData.jsonData 85056
      [functor, unit, cofibration]
  fibrant :
    recovered_closed_binder_type%
      DaggerRecoveredUnitaryModelFoundationData.jsonData 85056
      [functor, unit, cofibration, weakEquivalence]

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerUnitaryInvariance.FunctorialFibrantReplacement)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerUnitaryInvariance.FunctorialFibrantReplacement._sizeOf_1)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerUnitaryInvariance.FunctorialFibrantReplacement._sizeOf_inst)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerUnitaryInvariance.FunctorialFibrantReplacement.casesOn)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerUnitaryInvariance.FunctorialFibrantReplacement.cofibration)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerUnitaryInvariance.FunctorialFibrantReplacement.ctorIdx)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerUnitaryInvariance.FunctorialFibrantReplacement.fibrant)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerUnitaryInvariance.FunctorialFibrantReplacement.functor)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerUnitaryInvariance.FunctorialFibrantReplacement.mk)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerUnitaryInvariance.FunctorialFibrantReplacement.mk._flat_ctor)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerUnitaryInvariance.FunctorialFibrantReplacement.mk.inj)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerUnitaryInvariance.FunctorialFibrantReplacement.mk.injEq)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerUnitaryInvariance.FunctorialFibrantReplacement.mk.noConfusion)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerUnitaryInvariance.FunctorialFibrantReplacement.mk.sizeOf_spec)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerUnitaryInvariance.FunctorialFibrantReplacement.noConfusion)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerUnitaryInvariance.FunctorialFibrantReplacement.noConfusionType)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerUnitaryInvariance.FunctorialFibrantReplacement.rec)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerUnitaryInvariance.FunctorialFibrantReplacement.recOn)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerUnitaryInvariance.FunctorialFibrantReplacement.unit)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerUnitaryInvariance.FunctorialFibrantReplacement.weakEquivalence)
  pure ()

noncomputable def DaggerUnitaryInvariance.CoherentlyUnitary.{u}
    (arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryModelFoundationData.jsonData 85061
        [])
    (arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryModelFoundationData.jsonData 85061
        [arg0])
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryModelFoundationData.jsonData 85061
        [arg0, arg1])
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryModelFoundationData.jsonData 85061
        [arg0, arg1, arg2])
    (arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryModelFoundationData.jsonData 85061
        [arg0, arg1, arg2, arg3])
    :
    recovered_closed_result_type%
      DaggerRecoveredUnitaryModelFoundationData.jsonData 85061
      [arg0, arg1, arg2, arg3, arg4]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 85061 :=
    @(recovered_unitary_private_expr%
      DaggerRecoveredUnitaryModelFoundationData.jsonData 85082)
  exact @f arg0 arg1 arg2 arg3 arg4

theorem DaggerUnitaryInvariance.witnessAt_invariance.{u} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 85849 :=
  @(recovered_unitary_private_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 86762)

theorem DaggerUnitaryInvariance.hasIntervalWitness_invariance.{u} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 85680 :=
  @(recovered_unitary_private_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 85782)

theorem DaggerUnitaryInvariance.coherentlyUnitary_independent.{u} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 85212 :=
  @(recovered_unitary_private_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 85254)

theorem DaggerUnitaryInvariance.invariance.{u} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 85414 :=
  @(recovered_unitary_private_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 85569)

noncomputable def DaggerUnitaryInvariance.CoherentlyUnitaryVertex.{u}
    (arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryModelFoundationData.jsonData 85822
        [])
    (arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryModelFoundationData.jsonData 85822
        [arg0])
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryModelFoundationData.jsonData 85822
        [arg0, arg1])
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryModelFoundationData.jsonData 85822
        [arg0, arg1, arg2])
    (arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryModelFoundationData.jsonData 85822
        [arg0, arg1, arg2, arg3])
    :
    recovered_closed_result_type%
      DaggerRecoveredUnitaryModelFoundationData.jsonData 85822
      [arg0, arg1, arg2, arg3, arg4]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 85822 :=
    @(recovered_unitary_private_expr%
      DaggerRecoveredUnitaryModelFoundationData.jsonData 85828)
  exact @f arg0 arg1 arg2 arg3 arg4

theorem DaggerUnitaryInvariance.coherentlyUnitary_iff_receptacle.{u} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 87306 :=
  @(recovered_unitary_private_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 87367)

