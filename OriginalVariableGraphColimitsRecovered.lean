import OriginalVariableHomDiagramRecovered
import OriginalRecoveredClosedExpressionApplication
import OriginalRecoveredGlobalHornTransfiniteHomData

/-! Original VariableGraphColimits, with unchanged closed types and values. -/

set_option autoImplicit false
set_option maxRecDepth 100000

noncomputable abbrev DaggerVariableHomColimits.total.{u}
    (arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalHornTransfiniteHomData.jsonData 6742
        [])
    (arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalHornTransfiniteHomData.jsonData 6742
        [arg0])
    :
    recovered_closed_result_type%
      DaggerRecoveredGlobalHornTransfiniteHomData.jsonData 6742
      [arg0, arg1]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredGlobalHornTransfiniteHomData.jsonData 6742 :=
    @(recovered_closed_expr%
      DaggerRecoveredGlobalHornTransfiniteHomData.jsonData 6754)
  exact @f arg0 arg1

noncomputable abbrev DaggerVariableHomColimits.embed.{u}
    (arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalHornTransfiniteHomData.jsonData 6221
        [])
    (arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalHornTransfiniteHomData.jsonData 6221
        [arg0])
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalHornTransfiniteHomData.jsonData 6221
        [arg0, arg1])
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalHornTransfiniteHomData.jsonData 6221
        [arg0, arg1, arg2])
    (arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalHornTransfiniteHomData.jsonData 6221
        [arg0, arg1, arg2, arg3])
    :
    recovered_closed_result_type%
      DaggerRecoveredGlobalHornTransfiniteHomData.jsonData 6221
      [arg0, arg1, arg2, arg3, arg4]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredGlobalHornTransfiniteHomData.jsonData 6221 :=
    @(recovered_closed_expr%
      DaggerRecoveredGlobalHornTransfiniteHomData.jsonData 6250)
  exact @f arg0 arg1 arg2 arg3 arg4

noncomputable abbrev DaggerVariableHomColimits.graphValue.{u}
    (arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalHornTransfiniteHomData.jsonData 7303
        [])
    :
    recovered_closed_result_type%
      DaggerRecoveredGlobalHornTransfiniteHomData.jsonData 7303
      [arg0]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredGlobalHornTransfiniteHomData.jsonData 7303 :=
    @(recovered_closed_expr%
      DaggerRecoveredGlobalHornTransfiniteHomData.jsonData 7362)
  exact @f arg0

noncomputable abbrev DaggerVariableHomColimits.edgeDiagram.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalHornTransfiniteHomData.jsonData 7787
        []}
    [arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalHornTransfiniteHomData.jsonData 7787
        [arg0]]
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalHornTransfiniteHomData.jsonData 7787
        [arg0, arg1])
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalHornTransfiniteHomData.jsonData 7787
        [arg0, arg1, arg2])
    :
    recovered_closed_result_type%
      DaggerRecoveredGlobalHornTransfiniteHomData.jsonData 7787
      [arg0, arg1, arg2, arg3]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredGlobalHornTransfiniteHomData.jsonData 7787 :=
    @(recovered_closed_expr%
      DaggerRecoveredGlobalHornTransfiniteHomData.jsonData 7799)
  exact @f arg0 arg1 arg2 arg3

theorem DaggerVariableHomColimits.embed_cast.{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalHornTransfiniteHomData.jsonData 7417 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalHornTransfiniteHomData.jsonData 7752)

theorem DaggerVariableHomColimits.embed_map.{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalHornTransfiniteHomData.jsonData 6335 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalHornTransfiniteHomData.jsonData 6388)

noncomputable abbrev DaggerVariableHomColimits.vertexDiagram.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalHornTransfiniteHomData.jsonData 7286
        []}
    [arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalHornTransfiniteHomData.jsonData 7286
        [arg0]]
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalHornTransfiniteHomData.jsonData 7286
        [arg0, arg1])
    :
    recovered_closed_result_type%
      DaggerRecoveredGlobalHornTransfiniteHomData.jsonData 7286
      [arg0, arg1, arg2]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredGlobalHornTransfiniteHomData.jsonData 7286 :=
    @(recovered_closed_expr%
      DaggerRecoveredGlobalHornTransfiniteHomData.jsonData 7297)
  exact @f arg0 arg1 arg2

noncomputable abbrev DaggerVariableHomColimits.vertexCocone.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalHornTransfiniteHomData.jsonData 6769
        []}
    [arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalHornTransfiniteHomData.jsonData 6769
        [arg0]]
    {arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalHornTransfiniteHomData.jsonData 6769
        [arg0, arg1]}
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalHornTransfiniteHomData.jsonData 6769
        [arg0, arg1, arg2])
    :
    recovered_closed_result_type%
      DaggerRecoveredGlobalHornTransfiniteHomData.jsonData 6769
      [arg0, arg1, arg2, arg3]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredGlobalHornTransfiniteHomData.jsonData 6769 :=
    @(recovered_closed_expr%
      DaggerRecoveredGlobalHornTransfiniteHomData.jsonData 6783)
  exact @f arg0 arg1 arg2 arg3

theorem DaggerVariableHomColimits.graphValueIsColimit._proof_1.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredGlobalHornTransfiniteHomData.jsonData 6867 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalHornTransfiniteHomData.jsonData 7037)

noncomputable def DaggerVariableHomColimits.graphValueIsColimit.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalHornTransfiniteHomData.jsonData 6715
        []}
    [arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalHornTransfiniteHomData.jsonData 6715
        [arg0]]
    [arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalHornTransfiniteHomData.jsonData 6715
        [arg0, arg1]]
    {arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalHornTransfiniteHomData.jsonData 6715
        [arg0, arg1, arg2]}
    {arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalHornTransfiniteHomData.jsonData 6715
        [arg0, arg1, arg2, arg3]}
    (arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalHornTransfiniteHomData.jsonData 6715
        [arg0, arg1, arg2, arg3, arg4])
    (arg6 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalHornTransfiniteHomData.jsonData 6715
        [arg0, arg1, arg2, arg3, arg4, arg5])
    :
    recovered_closed_result_type%
      DaggerRecoveredGlobalHornTransfiniteHomData.jsonData 6715
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredGlobalHornTransfiniteHomData.jsonData 6715 :=
    @(recovered_closed_expr%
      DaggerRecoveredGlobalHornTransfiniteHomData.jsonData 6740)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5 arg6

noncomputable def DaggerVariableHomColimits.vertexIsColimit.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalHornTransfiniteHomData.jsonData 6428
        []}
    [arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalHornTransfiniteHomData.jsonData 6428
        [arg0]]
    [arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalHornTransfiniteHomData.jsonData 6428
        [arg0, arg1]]
    {arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalHornTransfiniteHomData.jsonData 6428
        [arg0, arg1, arg2]}
    {arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalHornTransfiniteHomData.jsonData 6428
        [arg0, arg1, arg2, arg3]}
    (arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalHornTransfiniteHomData.jsonData 6428
        [arg0, arg1, arg2, arg3, arg4])
    :
    recovered_closed_result_type%
      DaggerRecoveredGlobalHornTransfiniteHomData.jsonData 6428
      [arg0, arg1, arg2, arg3, arg4, arg5]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredGlobalHornTransfiniteHomData.jsonData 6428 :=
    @(recovered_closed_expr%
      DaggerRecoveredGlobalHornTransfiniteHomData.jsonData 6447)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5

noncomputable abbrev DaggerVariableHomColimits.edgeCocone.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalHornTransfiniteHomData.jsonData 7764
        []}
    [arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalHornTransfiniteHomData.jsonData 7764
        [arg0]]
    {arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalHornTransfiniteHomData.jsonData 7764
        [arg0, arg1]}
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalHornTransfiniteHomData.jsonData 7764
        [arg0, arg1, arg2])
    (arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalHornTransfiniteHomData.jsonData 7764
        [arg0, arg1, arg2, arg3])
    :
    recovered_closed_result_type%
      DaggerRecoveredGlobalHornTransfiniteHomData.jsonData 7764
      [arg0, arg1, arg2, arg3, arg4]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredGlobalHornTransfiniteHomData.jsonData 7764 :=
    @(recovered_closed_expr%
      DaggerRecoveredGlobalHornTransfiniteHomData.jsonData 7779)
  exact @f arg0 arg1 arg2 arg3 arg4

noncomputable def DaggerVariableHomColimits.edgeIsColimit.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalHornTransfiniteHomData.jsonData 6470
        []}
    [arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalHornTransfiniteHomData.jsonData 6470
        [arg0]]
    [arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalHornTransfiniteHomData.jsonData 6470
        [arg0, arg1]]
    {arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalHornTransfiniteHomData.jsonData 6470
        [arg0, arg1, arg2]}
    {arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalHornTransfiniteHomData.jsonData 6470
        [arg0, arg1, arg2, arg3]}
    (arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalHornTransfiniteHomData.jsonData 6470
        [arg0, arg1, arg2, arg3, arg4])
    (arg6 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalHornTransfiniteHomData.jsonData 6470
        [arg0, arg1, arg2, arg3, arg4, arg5])
    :
    recovered_closed_result_type%
      DaggerRecoveredGlobalHornTransfiniteHomData.jsonData 6470
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredGlobalHornTransfiniteHomData.jsonData 6470 :=
    @(recovered_closed_expr%
      DaggerRecoveredGlobalHornTransfiniteHomData.jsonData 6490)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5 arg6

theorem DaggerVariableHomColimits.embed_leg.{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalHornTransfiniteHomData.jsonData 6613 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalHornTransfiniteHomData.jsonData 6684)

theorem DaggerVariableHomColimits.object_jointly_surjective.{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalHornTransfiniteHomData.jsonData 7085 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalHornTransfiniteHomData.jsonData 7113)

theorem DaggerVariableHomColimits.embed_injective.{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalHornTransfiniteHomData.jsonData 7126 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalHornTransfiniteHomData.jsonData 7281)

theorem DaggerVariableHomColimits.vertex_leg.{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalHornTransfiniteHomData.jsonData 7892 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalHornTransfiniteHomData.jsonData 7901)

