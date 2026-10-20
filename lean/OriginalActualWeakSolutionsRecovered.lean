import OriginalActualWeakPresentationsRecovered
import OriginalRecoveredClosedExpressionApplication
import OriginalRecoveredActualWeakPipelineData

/-! Original ActualWeakSolutions, with unchanged closed types and values. -/

set_option autoImplicit false
set_option maxRecDepth 100000

noncomputable def DaggerActualWeakAccessibility.solution.{u}
    (arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredActualWeakPipelineData.jsonData 15660
        [])
    :
    recovered_closed_result_type%
      DaggerRecoveredActualWeakPipelineData.jsonData 15660
      [arg0]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredActualWeakPipelineData.jsonData 15660 :=
    @(recovered_closed_expr%
      DaggerRecoveredActualWeakPipelineData.jsonData 15675)
  exact @f arg0

noncomputable abbrev DaggerActualWeakAccessibility.standardSolution.{u}
    :
    recovered_closed_result_type%
      DaggerRecoveredActualWeakPipelineData.jsonData 15656
      []
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredActualWeakPipelineData.jsonData 15656 :=
    @(recovered_closed_expr%
      DaggerRecoveredActualWeakPipelineData.jsonData 15658)
  exact @f

theorem DaggerActualWeakAccessibility.solution_factor.{u} :
  recovered_closed_expr%
    DaggerRecoveredActualWeakPipelineData.jsonData 15825 :=
  @(recovered_closed_expr%
    DaggerRecoveredActualWeakPipelineData.jsonData 16403)

theorem DaggerActualWeakAccessibility.standard_solution_factor.{u} :
  recovered_closed_expr%
    DaggerRecoveredActualWeakPipelineData.jsonData 16468 :=
  @(recovered_closed_expr%
    DaggerRecoveredActualWeakPipelineData.jsonData 16478)

theorem DaggerActualWeakAccessibility.solution_rank.{u} :
  recovered_closed_expr%
    DaggerRecoveredActualWeakPipelineData.jsonData 16506 :=
  @(recovered_closed_expr%
    DaggerRecoveredActualWeakPipelineData.jsonData 16516)

theorem DaggerActualWeakAccessibility.solution_weak.{u} :
  recovered_closed_expr%
    DaggerRecoveredActualWeakPipelineData.jsonData 16537 :=
  @(recovered_closed_expr%
    DaggerRecoveredActualWeakPipelineData.jsonData 16548)

