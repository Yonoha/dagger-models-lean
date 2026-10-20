import OriginalUnitaryCompositionMapsUnifiedRecovered
import OriginalRecoveredClosedExpressionApplication
import OriginalRecoveredFullGlobalJCellClosureData

/-! Original UnitaryCompositionWitness, with unchanged closed types and values. -/

set_option autoImplicit false
set_option maxRecDepth 100000

theorem DaggerUnitaryComposition.witnessPointComm.{u} :
  recovered_closed_expr%
    DaggerRecoveredFullGlobalJCellClosureData.jsonData 8320 :=
  @(recovered_closed_expr%
    DaggerRecoveredFullGlobalJCellClosureData.jsonData 8381)

noncomputable def DaggerUnitaryComposition.chi.{u}
    (arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredFullGlobalJCellClosureData.jsonData 11060
        [])
    (arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredFullGlobalJCellClosureData.jsonData 11060
        [arg0])
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredFullGlobalJCellClosureData.jsonData 11060
        [arg0, arg1])
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredFullGlobalJCellClosureData.jsonData 11060
        [arg0, arg1, arg2])
    (arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredFullGlobalJCellClosureData.jsonData 11060
        [arg0, arg1, arg2, arg3])
    (arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredFullGlobalJCellClosureData.jsonData 11060
        [arg0, arg1, arg2, arg3, arg4])
    (arg6 :
      recovered_closed_binder_type%
        DaggerRecoveredFullGlobalJCellClosureData.jsonData 11060
        [arg0, arg1, arg2, arg3, arg4, arg5])
    (arg7 :
      recovered_closed_binder_type%
        DaggerRecoveredFullGlobalJCellClosureData.jsonData 11060
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6])
    {arg8 :
      recovered_closed_binder_type%
        DaggerRecoveredFullGlobalJCellClosureData.jsonData 11060
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7]}
    (arg9 :
      recovered_closed_binder_type%
        DaggerRecoveredFullGlobalJCellClosureData.jsonData 11060
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8])
    (arg10 :
      recovered_closed_binder_type%
        DaggerRecoveredFullGlobalJCellClosureData.jsonData 11060
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9])
    (arg11 :
      recovered_closed_binder_type%
        DaggerRecoveredFullGlobalJCellClosureData.jsonData 11060
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10])
    :
    recovered_closed_result_type%
      DaggerRecoveredFullGlobalJCellClosureData.jsonData 11060
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredFullGlobalJCellClosureData.jsonData 11060 :=
    @(recovered_closed_expr%
      DaggerRecoveredFullGlobalJCellClosureData.jsonData 11088)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5 arg6 arg7 arg8 arg9 arg10 arg11

theorem DaggerUnitaryComposition.chi_left.{u} :
  recovered_closed_expr%
    DaggerRecoveredFullGlobalJCellClosureData.jsonData 9086 :=
  @(recovered_closed_expr%
    DaggerRecoveredFullGlobalJCellClosureData.jsonData 9114)

theorem DaggerUnitaryComposition.chi_left_obj.{u} :
  recovered_closed_expr%
    DaggerRecoveredFullGlobalJCellClosureData.jsonData 9879 :=
  @(recovered_closed_expr%
    DaggerRecoveredFullGlobalJCellClosureData.jsonData 9950)

theorem DaggerUnitaryComposition.chi_right.{u} :
  recovered_closed_expr%
    DaggerRecoveredFullGlobalJCellClosureData.jsonData 7572 :=
  @(recovered_closed_expr%
    DaggerRecoveredFullGlobalJCellClosureData.jsonData 7617)

theorem DaggerUnitaryComposition.chi_right_obj.{u} :
  recovered_closed_expr%
    DaggerRecoveredFullGlobalJCellClosureData.jsonData 11549 :=
  @(recovered_closed_expr%
    DaggerRecoveredFullGlobalJCellClosureData.jsonData 11619)

theorem DaggerUnitaryComposition.outer_obj.{u} :
  recovered_closed_expr%
    DaggerRecoveredFullGlobalJCellClosureData.jsonData 11316 :=
  @(recovered_closed_expr%
    DaggerRecoveredFullGlobalJCellClosureData.jsonData 11476)

noncomputable def DaggerUnitaryComposition.outerMap.{u}
    (arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredFullGlobalJCellClosureData.jsonData 8272
        [])
    (arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredFullGlobalJCellClosureData.jsonData 8272
        [arg0])
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredFullGlobalJCellClosureData.jsonData 8272
        [arg0, arg1])
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredFullGlobalJCellClosureData.jsonData 8272
        [arg0, arg1, arg2])
    (arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredFullGlobalJCellClosureData.jsonData 8272
        [arg0, arg1, arg2, arg3])
    (arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredFullGlobalJCellClosureData.jsonData 8272
        [arg0, arg1, arg2, arg3, arg4])
    (arg6 :
      recovered_closed_binder_type%
        DaggerRecoveredFullGlobalJCellClosureData.jsonData 8272
        [arg0, arg1, arg2, arg3, arg4, arg5])
    (arg7 :
      recovered_closed_binder_type%
        DaggerRecoveredFullGlobalJCellClosureData.jsonData 8272
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6])
    {arg8 :
      recovered_closed_binder_type%
        DaggerRecoveredFullGlobalJCellClosureData.jsonData 8272
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7]}
    (arg9 :
      recovered_closed_binder_type%
        DaggerRecoveredFullGlobalJCellClosureData.jsonData 8272
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8])
    (arg10 :
      recovered_closed_binder_type%
        DaggerRecoveredFullGlobalJCellClosureData.jsonData 8272
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9])
    (arg11 :
      recovered_closed_binder_type%
        DaggerRecoveredFullGlobalJCellClosureData.jsonData 8272
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10])
    :
    recovered_closed_result_type%
      DaggerRecoveredFullGlobalJCellClosureData.jsonData 8272
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredFullGlobalJCellClosureData.jsonData 8272 :=
    @(recovered_closed_expr%
      DaggerRecoveredFullGlobalJCellClosureData.jsonData 8284)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5 arg6 arg7 arg8 arg9 arg10 arg11

theorem DaggerUnitaryComposition.outerMap_triangle.{u} :
  recovered_closed_expr%
    DaggerRecoveredFullGlobalJCellClosureData.jsonData 6097 :=
  @(recovered_closed_expr%
    DaggerRecoveredFullGlobalJCellClosureData.jsonData 6133)

theorem DaggerUnitaryComposition.liftHom_eval.{u} :
  recovered_closed_expr%
    DaggerRecoveredFullGlobalJCellClosureData.jsonData 6219 :=
  @(recovered_closed_expr%
    DaggerRecoveredFullGlobalJCellClosureData.jsonData 6733)

theorem DaggerUnitaryComposition.chi_left_map.{u} :
  recovered_closed_expr%
    DaggerRecoveredFullGlobalJCellClosureData.jsonData 6855 :=
  @(recovered_closed_expr%
    DaggerRecoveredFullGlobalJCellClosureData.jsonData 7465)

theorem DaggerUnitaryComposition.firstImage._proof_1.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredFullGlobalJCellClosureData.jsonData 8469 :=
  @(recovered_closed_expr%
    DaggerRecoveredFullGlobalJCellClosureData.jsonData 8475)

noncomputable def DaggerUnitaryComposition.glue.{u}
    (arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredFullGlobalJCellClosureData.jsonData 11229
        [])
    (arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredFullGlobalJCellClosureData.jsonData 11229
        [arg0])
    {arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredFullGlobalJCellClosureData.jsonData 11229
        [arg0, arg1]}
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredFullGlobalJCellClosureData.jsonData 11229
        [arg0, arg1, arg2])
    (arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredFullGlobalJCellClosureData.jsonData 11229
        [arg0, arg1, arg2, arg3])
    (arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredFullGlobalJCellClosureData.jsonData 11229
        [arg0, arg1, arg2, arg3, arg4])
    :
    recovered_closed_result_type%
      DaggerRecoveredFullGlobalJCellClosureData.jsonData 11229
      [arg0, arg1, arg2, arg3, arg4, arg5]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredFullGlobalJCellClosureData.jsonData 11229 :=
    @(recovered_closed_expr%
      DaggerRecoveredFullGlobalJCellClosureData.jsonData 11290)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5

noncomputable def DaggerUnitaryComposition.firstImage.{u}
    (arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredFullGlobalJCellClosureData.jsonData 7506
        [])
    (arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredFullGlobalJCellClosureData.jsonData 7506
        [arg0])
    {arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredFullGlobalJCellClosureData.jsonData 7506
        [arg0, arg1]}
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredFullGlobalJCellClosureData.jsonData 7506
        [arg0, arg1, arg2])
    (arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredFullGlobalJCellClosureData.jsonData 7506
        [arg0, arg1, arg2, arg3])
    (arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredFullGlobalJCellClosureData.jsonData 7506
        [arg0, arg1, arg2, arg3, arg4])
    :
    recovered_closed_result_type%
      DaggerRecoveredFullGlobalJCellClosureData.jsonData 7506
      [arg0, arg1, arg2, arg3, arg4, arg5]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredFullGlobalJCellClosureData.jsonData 7506 :=
    @(recovered_closed_expr%
      DaggerRecoveredFullGlobalJCellClosureData.jsonData 7545)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5

theorem DaggerUnitaryComposition.firstImage_chi.{u} :
  recovered_closed_expr%
    DaggerRecoveredFullGlobalJCellClosureData.jsonData 9129 :=
  @(recovered_closed_expr%
    DaggerRecoveredFullGlobalJCellClosureData.jsonData 9502)

theorem DaggerUnitaryComposition.chi_right_map.{u} :
  recovered_closed_expr%
    DaggerRecoveredFullGlobalJCellClosureData.jsonData 8561 :=
  @(recovered_closed_expr%
    DaggerRecoveredFullGlobalJCellClosureData.jsonData 9064)

theorem DaggerUnitaryComposition.composite_chi_map.{u} :
  recovered_closed_expr%
    DaggerRecoveredFullGlobalJCellClosureData.jsonData 7786 :=
  @(recovered_closed_expr%
    DaggerRecoveredFullGlobalJCellClosureData.jsonData 8224)

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerUnitaryComposition.outerMap.eq_1)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerUnitaryComposition.firstImage.eq_1)
  pure ()

noncomputable def DaggerUnitaryComposition.compositeVertex.{u}
    (arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredFullGlobalJCellClosureData.jsonData 11486
        [])
    (arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredFullGlobalJCellClosureData.jsonData 11486
        [arg0])
    {arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredFullGlobalJCellClosureData.jsonData 11486
        [arg0, arg1]}
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredFullGlobalJCellClosureData.jsonData 11486
        [arg0, arg1, arg2])
    (arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredFullGlobalJCellClosureData.jsonData 11486
        [arg0, arg1, arg2, arg3])
    (arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredFullGlobalJCellClosureData.jsonData 11486
        [arg0, arg1, arg2, arg3, arg4])
    :
    recovered_closed_result_type%
      DaggerRecoveredFullGlobalJCellClosureData.jsonData 11486
      [arg0, arg1, arg2, arg3, arg4, arg5]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredFullGlobalJCellClosureData.jsonData 11486 :=
    @(recovered_closed_expr%
      DaggerRecoveredFullGlobalJCellClosureData.jsonData 11531)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5

theorem DaggerUnitaryComposition.realized_generator.{u} :
  recovered_closed_expr%
    DaggerRecoveredFullGlobalJCellClosureData.jsonData 11694 :=
  @(recovered_closed_expr%
    DaggerRecoveredFullGlobalJCellClosureData.jsonData 11936)

theorem DaggerUnitaryComposition.composite_image.{u} :
  recovered_closed_expr%
    DaggerRecoveredFullGlobalJCellClosureData.jsonData 10001 :=
  @(recovered_closed_expr%
    DaggerRecoveredFullGlobalJCellClosureData.jsonData 10817)

theorem DaggerUnitaryComposition.outerMap_generator.{u} :
  recovered_closed_expr%
    DaggerRecoveredFullGlobalJCellClosureData.jsonData 10836 :=
  @(recovered_closed_expr%
    DaggerRecoveredFullGlobalJCellClosureData.jsonData 11046)

theorem DaggerUnitaryComposition.outerMap_J.{u} :
  recovered_closed_expr%
    DaggerRecoveredFullGlobalJCellClosureData.jsonData 9708 :=
  @(recovered_closed_expr%
    DaggerRecoveredFullGlobalJCellClosureData.jsonData 9861)

theorem DaggerUnitaryComposition.chi_unique.{u} :
  recovered_closed_expr%
    DaggerRecoveredFullGlobalJCellClosureData.jsonData 11128 :=
  @(recovered_closed_expr%
    DaggerRecoveredFullGlobalJCellClosureData.jsonData 11220)

