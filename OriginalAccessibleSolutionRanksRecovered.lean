import OriginalN0CommonCardinalsRecovered
import OriginalRLPArrowRecovered
import OriginalSmithSolutionsRecovered
import OriginalRecoveredClosedExpressionApplication
import OriginalRecoveredAccessibleSolutionPipelineData

/-! Original AccessibleSolutionRanks, with unchanged closed types and values. -/

set_option autoImplicit false
set_option maxRecDepth 100000

noncomputable abbrev DaggerAccessibleSolutions.arrowProperty.{v, u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredAccessibleSolutionPipelineData.jsonData 17233
        []}
    [arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredAccessibleSolutionPipelineData.jsonData 17233
        [arg0]]
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredAccessibleSolutionPipelineData.jsonData 17233
        [arg0, arg1])
    :
    recovered_closed_result_type%
      DaggerRecoveredAccessibleSolutionPipelineData.jsonData 17233
      [arg0, arg1, arg2]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredAccessibleSolutionPipelineData.jsonData 17233 :=
    @(recovered_closed_expr%
      DaggerRecoveredAccessibleSolutionPipelineData.jsonData 17281)
  exact @f arg0 arg1 arg2

theorem DaggerAccessibleSolutions.exists_solution_rank.{w, v, u} :
  recovered_closed_expr%
    DaggerRecoveredAccessibleSolutionPipelineData.jsonData 16091 :=
  @(recovered_closed_expr%
    DaggerRecoveredAccessibleSolutionPipelineData.jsonData 17216)

