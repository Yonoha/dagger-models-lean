import OriginalUnitaryCompositionWitnessUnifiedRecovered
import OriginalRecoveredClosedExpressionApplication
import OriginalRecoveredFullGlobalJCellClosureData

/-! Original UnitaryComposition, with unchanged closed types and values. -/

set_option autoImplicit false
set_option maxRecDepth 100000

theorem DaggerUnitaryComposition.pushout_allHomGood.{u} :
  recovered_closed_expr%
    DaggerRecoveredFullGlobalJCellClosureData.jsonData 13498 :=
  @(recovered_closed_expr%
    DaggerRecoveredFullGlobalJCellClosureData.jsonData 13518)

theorem DaggerUnitaryComposition.compositeExtraction._proof_1.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredFullGlobalJCellClosureData.jsonData 13581 :=
  @(recovered_closed_expr%
    DaggerRecoveredFullGlobalJCellClosureData.jsonData 13604)

theorem DaggerUnitaryComposition.compositeExtraction._proof_2.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredFullGlobalJCellClosureData.jsonData 13644 :=
  @(recovered_closed_expr%
    DaggerRecoveredFullGlobalJCellClosureData.jsonData 13653)

noncomputable def DaggerUnitaryComposition.compositeExtraction.{u}
    (arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredFullGlobalJCellClosureData.jsonData 13613
        [])
    (arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredFullGlobalJCellClosureData.jsonData 13613
        [arg0])
    {arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredFullGlobalJCellClosureData.jsonData 13613
        [arg0, arg1]}
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredFullGlobalJCellClosureData.jsonData 13613
        [arg0, arg1, arg2])
    (arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredFullGlobalJCellClosureData.jsonData 13613
        [arg0, arg1, arg2, arg3])
    (arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredFullGlobalJCellClosureData.jsonData 13613
        [arg0, arg1, arg2, arg3, arg4])
    :
    recovered_closed_result_type%
      DaggerRecoveredFullGlobalJCellClosureData.jsonData 13613
      [arg0, arg1, arg2, arg3, arg4, arg5]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredFullGlobalJCellClosureData.jsonData 13613 :=
    @(recovered_closed_expr%
      DaggerRecoveredFullGlobalJCellClosureData.jsonData 13638)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5

theorem DaggerUnitaryComposition.compositeExtraction_fac.{u} :
  recovered_closed_expr%
    DaggerRecoveredFullGlobalJCellClosureData.jsonData 11977 :=
  @(recovered_closed_expr%
    DaggerRecoveredFullGlobalJCellClosureData.jsonData 11987)

noncomputable def DaggerUnitaryComposition.compositeCopyMap.{u}
    (arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredFullGlobalJCellClosureData.jsonData 14220
        [])
    (arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredFullGlobalJCellClosureData.jsonData 14220
        [arg0])
    {arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredFullGlobalJCellClosureData.jsonData 14220
        [arg0, arg1]}
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredFullGlobalJCellClosureData.jsonData 14220
        [arg0, arg1, arg2])
    (arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredFullGlobalJCellClosureData.jsonData 14220
        [arg0, arg1, arg2, arg3])
    (arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredFullGlobalJCellClosureData.jsonData 14220
        [arg0, arg1, arg2, arg3, arg4])
    (arg6 :
      recovered_closed_binder_type%
        DaggerRecoveredFullGlobalJCellClosureData.jsonData 14220
        [arg0, arg1, arg2, arg3, arg4, arg5])
    (arg7 :
      recovered_closed_binder_type%
        DaggerRecoveredFullGlobalJCellClosureData.jsonData 14220
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6])
    (arg8 :
      recovered_closed_binder_type%
        DaggerRecoveredFullGlobalJCellClosureData.jsonData 14220
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7])
    (arg9 :
      recovered_closed_binder_type%
        DaggerRecoveredFullGlobalJCellClosureData.jsonData 14220
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8])
    (arg10 :
      recovered_closed_binder_type%
        DaggerRecoveredFullGlobalJCellClosureData.jsonData 14220
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9])
    (arg11 :
      recovered_closed_binder_type%
        DaggerRecoveredFullGlobalJCellClosureData.jsonData 14220
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10])
    :
    recovered_closed_result_type%
      DaggerRecoveredFullGlobalJCellClosureData.jsonData 14220
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredFullGlobalJCellClosureData.jsonData 14220 :=
    @(recovered_closed_expr%
      DaggerRecoveredFullGlobalJCellClosureData.jsonData 14250)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5 arg6 arg7 arg8 arg9 arg10 arg11

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerUnitaryComposition.compositeCopyMap.eq_1)
  pure ()

theorem DaggerUnitaryComposition.compositeCopyMap_J.{u} :
  recovered_closed_expr%
    DaggerRecoveredFullGlobalJCellClosureData.jsonData 13247 :=
  @(recovered_closed_expr%
    DaggerRecoveredFullGlobalJCellClosureData.jsonData 13491)

theorem DaggerUnitaryComposition.coherentlyUnitary_comp_realized.{u} :
  recovered_closed_expr%
    DaggerRecoveredFullGlobalJCellClosureData.jsonData 12057 :=
  @(recovered_closed_expr%
    DaggerRecoveredFullGlobalJCellClosureData.jsonData 12852)

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerUnitaryInvariance.CoherentlyUnitaryVertex.eq_1)
  pure ()

theorem DaggerUnitaryComposition.coherentlyUnitary_comp.{u} :
  recovered_closed_expr%
    DaggerRecoveredFullGlobalJCellClosureData.jsonData 13695 :=
  @(recovered_closed_expr%
    DaggerRecoveredFullGlobalJCellClosureData.jsonData 14175)

theorem DaggerUnitaryComposition.coherentlyUnitaryVertex_comp.{u} :
  recovered_closed_expr%
    DaggerRecoveredFullGlobalJCellClosureData.jsonData 12898 :=
  @(recovered_closed_expr%
    DaggerRecoveredFullGlobalJCellClosureData.jsonData 13005)

theorem DaggerUnitaryComposition.standard_coherentlyUnitary_comp.{u} :
  recovered_closed_expr%
    DaggerRecoveredFullGlobalJCellClosureData.jsonData 13029 :=
  @(recovered_closed_expr%
    DaggerRecoveredFullGlobalJCellClosureData.jsonData 13046)

