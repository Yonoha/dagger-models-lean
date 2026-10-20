import OriginalN0DirectedClosureRecovered
import OriginalRecoveredClosedExpressionApplication
import OriginalRecoveredAccessibleSolutionPipelineData

/-! Original N0DirectedHull, with unchanged closed types and values. -/

set_option autoImplicit false
set_option maxRecDepth 100000

theorem DaggerAccessibleInverseImage.closureStage._proof_1.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredAccessibleSolutionPipelineData.jsonData 3038 :=
  @(recovered_closed_expr%
    DaggerRecoveredAccessibleSolutionPipelineData.jsonData 3058)

theorem DaggerAccessibleInverseImage.closureStage._proof_2.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredAccessibleSolutionPipelineData.jsonData 2858 :=
  @(recovered_closed_expr%
    DaggerRecoveredAccessibleSolutionPipelineData.jsonData 2864)

noncomputable def DaggerAccessibleInverseImage.closureStage.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredAccessibleSolutionPipelineData.jsonData 2871
        []}
    [arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredAccessibleSolutionPipelineData.jsonData 2871
        [arg0]]
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredAccessibleSolutionPipelineData.jsonData 2871
        [arg0, arg1])
    [arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredAccessibleSolutionPipelineData.jsonData 2871
        [arg0, arg1, arg2]]
    [arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredAccessibleSolutionPipelineData.jsonData 2871
        [arg0, arg1, arg2, arg3]]
    (arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredAccessibleSolutionPipelineData.jsonData 2871
        [arg0, arg1, arg2, arg3, arg4])
    :
    recovered_closed_result_type%
      DaggerRecoveredAccessibleSolutionPipelineData.jsonData 2871
      [arg0, arg1, arg2, arg3, arg4, arg5]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredAccessibleSolutionPipelineData.jsonData 2871 :=
    @(recovered_closed_expr%
      DaggerRecoveredAccessibleSolutionPipelineData.jsonData 2933)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5

noncomputable def DaggerAccessibleInverseImage.directedHull.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredAccessibleSolutionPipelineData.jsonData 796
        []}
    [arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredAccessibleSolutionPipelineData.jsonData 796
        [arg0]]
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredAccessibleSolutionPipelineData.jsonData 796
        [arg0, arg1])
    [arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredAccessibleSolutionPipelineData.jsonData 796
        [arg0, arg1, arg2]]
    [arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredAccessibleSolutionPipelineData.jsonData 796
        [arg0, arg1, arg2, arg3]]
    (arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredAccessibleSolutionPipelineData.jsonData 796
        [arg0, arg1, arg2, arg3, arg4])
    :
    recovered_closed_result_type%
      DaggerRecoveredAccessibleSolutionPipelineData.jsonData 796
      [arg0, arg1, arg2, arg3, arg4, arg5]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredAccessibleSolutionPipelineData.jsonData 796 :=
    @(recovered_closed_expr%
      DaggerRecoveredAccessibleSolutionPipelineData.jsonData 2199)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerAccessibleInverseImage.closureStage.eq_1)
  pure ()

theorem DaggerAccessibleInverseImage.closureStage_eq.{u} :
  recovered_closed_expr%
    DaggerRecoveredAccessibleSolutionPipelineData.jsonData 3091 :=
  @(recovered_closed_expr%
    DaggerRecoveredAccessibleSolutionPipelineData.jsonData 3363)

theorem DaggerAccessibleInverseImage.closureStage_hasCardinalLT.{u} :
  recovered_closed_expr%
    DaggerRecoveredAccessibleSolutionPipelineData.jsonData 3377 :=
  @(recovered_closed_expr%
    DaggerRecoveredAccessibleSolutionPipelineData.jsonData 3552)

theorem DaggerAccessibleInverseImage.directedHull_hasCardinalLT.{u} :
  recovered_closed_expr%
    DaggerRecoveredAccessibleSolutionPipelineData.jsonData 2217 :=
  @(recovered_closed_expr%
    DaggerRecoveredAccessibleSolutionPipelineData.jsonData 2301)

theorem DaggerAccessibleInverseImage.closureStage_mono.{u} :
  recovered_closed_expr%
    DaggerRecoveredAccessibleSolutionPipelineData.jsonData 2344 :=
  @(recovered_closed_expr%
    DaggerRecoveredAccessibleSolutionPipelineData.jsonData 2666)

theorem DaggerAccessibleInverseImage.subset_closureStage.{u} :
  recovered_closed_expr%
    DaggerRecoveredAccessibleSolutionPipelineData.jsonData 2675 :=
  @(recovered_closed_expr%
    DaggerRecoveredAccessibleSolutionPipelineData.jsonData 2774)

theorem DaggerAccessibleInverseImage.subset_directedHull.{u} :
  recovered_closed_expr%
    DaggerRecoveredAccessibleSolutionPipelineData.jsonData 2946 :=
  @(recovered_closed_expr%
    DaggerRecoveredAccessibleSolutionPipelineData.jsonData 3024)

