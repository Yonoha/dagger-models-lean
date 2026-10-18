import OriginalUnitaryIntervalCountabilityRecovered
import FixedCategoryModel
import FixedGraphPlacementChecks
import Mathlib.AlgebraicTopology.SimplicialSet.FiniteColimits
import OriginalRecoveredClosedExpressionApplication
import OriginalRecoveredUnitaryPrivateExpression
import OriginalRecoveredUnitaryModelFoundationData

/-! Original UnitaryIntervalSOACountability, with unchanged closed types and values. -/

set_option autoImplicit false
set_option maxRecDepth 100000

theorem DaggerUnitaryInterval.countable_I_index.{u} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 12500 :=
  @(recovered_unitary_private_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 14782)

theorem DaggerUnitaryInterval.countable_freePlacementHom.{u} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 17749 :=
  @(recovered_unitary_private_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 18084)

theorem DaggerUnitaryInterval.countable_I_domainHom.{u} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 20438 :=
  @(recovered_unitary_private_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 20528)

theorem DaggerUnitaryInterval.countable_I_codomainHom.{u} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 19951 :=
  @(recovered_unitary_private_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 20429)

theorem DaggerUnitaryInterval.countable_liftingIndex.{u} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 14844 :=
  @(recovered_unitary_private_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 16971)

theorem DaggerRecoveredUnitaryPrivate.placementEq2.{u_1, u_2} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 17007 :=
  @(recovered_unitary_private_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 17014)

theorem DaggerUnitaryInterval.countable_free.{u} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 17694 :=
  @(recovered_unitary_private_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 17719)

noncomputable def DaggerUnitaryInterval.instLinearOrder_unitaryIntervalSOACountability.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryModelFoundationData.jsonData 17722
        []}
    :
    recovered_closed_result_type%
      DaggerRecoveredUnitaryModelFoundationData.jsonData 17722
      [arg0]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 17722 :=
    @(recovered_unitary_private_expr%
      DaggerRecoveredUnitaryModelFoundationData.jsonData 17724)
  exact @f arg0

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFixedGraphGenerators.placement.eq_2)
  pure ()

theorem DaggerUnitaryInterval.placement_finite.{u} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 18875 :=
  @(recovered_unitary_private_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 19851)

theorem DaggerUnitaryInterval.countable_freePlacement.{u} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 19872 :=
  @(recovered_unitary_private_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 19937)

theorem DaggerUnitaryInterval.countable_I_domain.{u} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 17024 :=
  @(recovered_unitary_private_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 17678)

theorem DaggerUnitaryInterval.countable_I_codomain.{u} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 20534 :=
  @(recovered_unitary_private_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 20606)

theorem DaggerUnitaryInterval.countable_successor.{u} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 18233 :=
  @(recovered_unitary_private_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 18796)

noncomputable abbrev DaggerRecoveredUnitaryPrivate.placementSplitter.{u_1, u_2}
    (arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryModelFoundationData.jsonData 18803
        [])
    (arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryModelFoundationData.jsonData 18803
        [arg0])
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryModelFoundationData.jsonData 18803
        [arg0, arg1])
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryModelFoundationData.jsonData 18803
        [arg0, arg1, arg2])
    (arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryModelFoundationData.jsonData 18803
        [arg0, arg1, arg2, arg3])
    :
    recovered_closed_result_type%
      DaggerRecoveredUnitaryModelFoundationData.jsonData 18803
      [arg0, arg1, arg2, arg3, arg4]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 18803 :=
    @(recovered_unitary_private_expr%
      DaggerRecoveredUnitaryModelFoundationData.jsonData 16994)
  exact @f arg0 arg1 arg2 arg3 arg4

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFixedGraphGenerators.placement.eq_1)
  pure ()

theorem DaggerRecoveredUnitaryPrivate.placementEq1.{u_1, u_2} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 18858 :=
  @(recovered_unitary_private_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 18865)

