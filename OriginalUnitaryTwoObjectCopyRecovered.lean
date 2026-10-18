import OriginalUnitaryIntervalsRecovered
import FixedCategoryConnectedColimits
import OriginalRecoveredClosedExpressionApplication
import OriginalRecoveredUnitaryPrivateExpression
import OriginalRecoveredUnitaryModelFoundationData

/-! Original UnitaryTwoObjectCopy, with unchanged closed types and values. -/

set_option autoImplicit false
set_option maxRecDepth 100000

noncomputable def DaggerUnitaryInvariance.endpoint.{u}
    (arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryModelFoundationData.jsonData 74506
        [])
    (arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryModelFoundationData.jsonData 74506
        [arg0])
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryModelFoundationData.jsonData 74506
        [arg0, arg1])
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryModelFoundationData.jsonData 74506
        [arg0, arg1, arg2])
    :
    recovered_closed_result_type%
      DaggerRecoveredUnitaryModelFoundationData.jsonData 74506
      [arg0, arg1, arg2, arg3]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 74506 :=
    @(recovered_unitary_private_expr%
      DaggerRecoveredUnitaryModelFoundationData.jsonData 74521)
  exact @f arg0 arg1 arg2 arg3

noncomputable def DaggerUnitaryInvariance.twoObjectCopy.{u}
    (arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryModelFoundationData.jsonData 74493
        [])
    (arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryModelFoundationData.jsonData 74493
        [arg0])
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryModelFoundationData.jsonData 74493
        [arg0, arg1])
    :
    recovered_closed_result_type%
      DaggerRecoveredUnitaryModelFoundationData.jsonData 74493
      [arg0, arg1, arg2]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 74493 :=
    @(recovered_unitary_private_expr%
      DaggerRecoveredUnitaryModelFoundationData.jsonData 74502)
  exact @f arg0 arg1 arg2

theorem DaggerUnitaryInvariance.JfromMap._proof_1.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 74580 :=
  @(recovered_unitary_private_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 74765)

theorem DaggerUnitaryInvariance.twoObjectMap._proof_1.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 76601 :=
  @(recovered_unitary_private_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 77035)

theorem DaggerUnitaryInvariance.twoObjectMap._proof_2.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 82009 :=
  @(recovered_unitary_private_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 82014)

theorem DaggerUnitaryInvariance.twoObjectMap._proof_3.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 82062 :=
  @(recovered_unitary_private_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 82067)

theorem DaggerUnitaryInvariance.twoObjectMap._proof_4.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 77095 :=
  @(recovered_unitary_private_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 79416)

noncomputable def DaggerUnitaryInvariance.twoObjectMap.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryModelFoundationData.jsonData 75931
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryModelFoundationData.jsonData 75931
        [arg0]}
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryModelFoundationData.jsonData 75931
        [arg0, arg1])
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryModelFoundationData.jsonData 75931
        [arg0, arg1, arg2])
    (arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryModelFoundationData.jsonData 75931
        [arg0, arg1, arg2, arg3])
    :
    recovered_closed_result_type%
      DaggerRecoveredUnitaryModelFoundationData.jsonData 75931
      [arg0, arg1, arg2, arg3, arg4]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 75931 :=
    @(recovered_unitary_private_expr%
      DaggerRecoveredUnitaryModelFoundationData.jsonData 75936)
  exact @f arg0 arg1 arg2 arg3 arg4

theorem DaggerUnitaryInvariance.twoObjectMap_weak.{u} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 74790 :=
  @(recovered_unitary_private_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 75340)

theorem DaggerUnitaryInvariance.twoObjectMap_inclusion.{u} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 82098 :=
  @(recovered_unitary_private_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 83564)

theorem DaggerUnitaryInvariance.twoObjectMap_id.{u} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 75367 :=
  @(recovered_unitary_private_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 75611)

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerUnitaryInvariance.twoObjectMap.eq_1)
  pure ()

theorem DaggerUnitaryInvariance.twoObjectMap_hom.{u} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 75974 :=
  @(recovered_unitary_private_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 76316)

noncomputable def DaggerUnitaryInvariance.JfromMap.{u}
    (arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryModelFoundationData.jsonData 83571
        [])
    (arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryModelFoundationData.jsonData 83571
        [arg0])
    :
    recovered_closed_result_type%
      DaggerRecoveredUnitaryModelFoundationData.jsonData 83571
      [arg0, arg1]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 83571 :=
    @(recovered_unitary_private_expr%
      DaggerRecoveredUnitaryModelFoundationData.jsonData 83630)
  exact @f arg0 arg1

theorem DaggerUnitaryInvariance.JfromMap_generator.{u} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 83644 :=
  @(recovered_unitary_private_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 83771)

theorem DaggerUnitaryInvariance.J_cofibrant.{u} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 80559 :=
  @(recovered_unitary_private_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 81956)
attribute [instance] DaggerUnitaryInvariance.J_cofibrant

theorem DaggerUnitaryInvariance.interval_cofibrant.{u} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 79473 :=
  @(recovered_unitary_private_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 79506)
attribute [instance] DaggerUnitaryInvariance.interval_cofibrant

theorem DaggerUnitaryInvariance.twoObjectMap_comp.{u} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 79559 :=
  @(recovered_unitary_private_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 80558)

