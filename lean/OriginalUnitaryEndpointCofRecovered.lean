import OriginalUnitaryTwoObjectCopyRecovered
import OriginalIinjBridgeRecovered
import DaggerModels.DaggerSmallObject
import OriginalRecoveredClosedExpressionApplication
import OriginalRecoveredUnitaryEndpointCofData

/-! Original UnitaryEndpointCof, with unchanged closed types and values. -/

set_option autoImplicit false
set_option maxRecDepth 100000

structure DaggerUnitaryEndpointCof.EndpointData.{u}
    (arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryEndpointCofData.jsonData 7677
        [])
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryEndpointCofData.jsonData 7677
        [arg0]}
    {arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryEndpointCofData.jsonData 7677
        [arg0, arg1]}
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryEndpointCofData.jsonData 7677
        [arg0, arg1, arg2])
    (arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryEndpointCofData.jsonData 7677
        [arg0, arg1, arg2, arg3])
    (arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryEndpointCofData.jsonData 7677
        [arg0, arg1, arg2, arg3, arg4])
    (arg6 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryEndpointCofData.jsonData 7677
        [arg0, arg1, arg2, arg3, arg4, arg5])
    :
      recovered_closed_result_type%
        DaggerRecoveredUnitaryEndpointCofData.jsonData 7677
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6] where
  x0 :
    recovered_closed_binder_type%
      DaggerRecoveredUnitaryEndpointCofData.jsonData 7842
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6]
  x1 :
    recovered_closed_binder_type%
      DaggerRecoveredUnitaryEndpointCofData.jsonData 7842
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, x0]
  image_left :
    recovered_closed_binder_type%
      DaggerRecoveredUnitaryEndpointCofData.jsonData 7842
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, x0, x1]
  image_right :
    recovered_closed_binder_type%
      DaggerRecoveredUnitaryEndpointCofData.jsonData 7842
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, x0, x1, image_left]
  selected :
    recovered_closed_binder_type%
      DaggerRecoveredUnitaryEndpointCofData.jsonData 7842
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, x0, x1, image_left, image_right]

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerUnitaryEndpointCof.EndpointData)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerUnitaryEndpointCof.EndpointData._sizeOf_1)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerUnitaryEndpointCof.EndpointData._sizeOf_inst)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerUnitaryEndpointCof.EndpointData.casesOn)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerUnitaryEndpointCof.EndpointData.ctorIdx)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerUnitaryEndpointCof.EndpointData.image_left)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerUnitaryEndpointCof.EndpointData.image_right)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerUnitaryEndpointCof.EndpointData.mk)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerUnitaryEndpointCof.EndpointData.mk._flat_ctor)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerUnitaryEndpointCof.EndpointData.mk.inj)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerUnitaryEndpointCof.EndpointData.mk.injEq)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerUnitaryEndpointCof.EndpointData.mk.noConfusion)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerUnitaryEndpointCof.EndpointData.mk.sizeOf_spec)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerUnitaryEndpointCof.EndpointData.noConfusion)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerUnitaryEndpointCof.EndpointData.noConfusionType)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerUnitaryEndpointCof.EndpointData.rec)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerUnitaryEndpointCof.EndpointData.recOn)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerUnitaryEndpointCof.EndpointData.selected)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerUnitaryEndpointCof.EndpointData.x0)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerUnitaryEndpointCof.EndpointData.x1)
  pure ()

theorem DaggerUnitaryEndpointCof.EndpointData.object_eq.{u} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryEndpointCofData.jsonData 623 :=
  @(recovered_closed_expr%
    DaggerRecoveredUnitaryEndpointCofData.jsonData 806)

noncomputable def DaggerUnitaryEndpointCof.localSquare.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryEndpointCofData.jsonData 213
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryEndpointCofData.jsonData 213
        [arg0]}
    {arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryEndpointCofData.jsonData 213
        [arg0, arg1]}
    {arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryEndpointCofData.jsonData 213
        [arg0, arg1, arg2]}
    {arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryEndpointCofData.jsonData 213
        [arg0, arg1, arg2, arg3]}
    {arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryEndpointCofData.jsonData 213
        [arg0, arg1, arg2, arg3, arg4]}
    {arg6 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryEndpointCofData.jsonData 213
        [arg0, arg1, arg2, arg3, arg4, arg5]}
    (arg7 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryEndpointCofData.jsonData 213
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6])
    :
    recovered_closed_result_type%
      DaggerRecoveredUnitaryEndpointCofData.jsonData 213
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredUnitaryEndpointCofData.jsonData 213 :=
    @(recovered_closed_expr%
      DaggerRecoveredUnitaryEndpointCofData.jsonData 254)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5 arg6 arg7

noncomputable def DaggerUnitaryEndpointCof.globalCellRetracts.{u}
    :
    recovered_closed_result_type%
      DaggerRecoveredUnitaryEndpointCofData.jsonData 2575
      []
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredUnitaryEndpointCofData.jsonData 2575 :=
    @(recovered_closed_expr%
      DaggerRecoveredUnitaryEndpointCofData.jsonData 2591)
  exact @f

theorem DaggerUnitaryEndpointCof.global_cof_eq_cellRetracts.{u} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryEndpointCofData.jsonData 4312 :=
  @(recovered_closed_expr%
    DaggerRecoveredUnitaryEndpointCofData.jsonData 4323)

theorem DaggerUnitaryEndpointCof.fixedLiftData._proof_4.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryEndpointCofData.jsonData 3132 :=
  @(recovered_closed_expr%
    DaggerRecoveredUnitaryEndpointCofData.jsonData 2451)

theorem DaggerUnitaryEndpointCof.fixedLiftData._proof_1.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryEndpointCofData.jsonData 3106 :=
  @(recovered_closed_expr%
    DaggerRecoveredUnitaryEndpointCofData.jsonData 3128)

theorem DaggerUnitaryEndpointCof.twoObjectMap_fibration.{u} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryEndpointCofData.jsonData 3330 :=
  @(recovered_closed_expr%
    DaggerRecoveredUnitaryEndpointCofData.jsonData 3836)

theorem DaggerUnitaryEndpointCof.fixedLiftData._proof_2.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryEndpointCofData.jsonData 3849 :=
  @(recovered_closed_expr%
    DaggerRecoveredUnitaryEndpointCofData.jsonData 3871)

theorem DaggerUnitaryEndpointCof.fixedLiftData._proof_3.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryEndpointCofData.jsonData 3202 :=
  @(recovered_closed_expr%
    DaggerRecoveredUnitaryEndpointCofData.jsonData 3258)

theorem DaggerUnitaryEndpointCof.fixedLiftData._proof_5.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryEndpointCofData.jsonData 5687 :=
  @(recovered_closed_expr%
    DaggerRecoveredUnitaryEndpointCofData.jsonData 5697)

theorem DaggerUnitaryEndpointCof.fixedLiftData._proof_6.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryEndpointCofData.jsonData 2432 :=
  @(recovered_closed_expr%
    DaggerRecoveredUnitaryEndpointCofData.jsonData 2505)

theorem DaggerUnitaryEndpointCof.fixedLiftData._proof_7.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryEndpointCofData.jsonData 4343 :=
  @(recovered_closed_expr%
    DaggerRecoveredUnitaryEndpointCofData.jsonData 4366)

noncomputable def DaggerUnitaryEndpointCof.fixedLiftData.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryEndpointCofData.jsonData 5842
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryEndpointCofData.jsonData 5842
        [arg0]}
    {arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryEndpointCofData.jsonData 5842
        [arg0, arg1]}
    {arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryEndpointCofData.jsonData 5842
        [arg0, arg1, arg2]}
    {arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryEndpointCofData.jsonData 5842
        [arg0, arg1, arg2, arg3]}
    {arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryEndpointCofData.jsonData 5842
        [arg0, arg1, arg2, arg3, arg4]}
    {arg6 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryEndpointCofData.jsonData 5842
        [arg0, arg1, arg2, arg3, arg4, arg5]}
    (arg7 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryEndpointCofData.jsonData 5842
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6])
    (arg8 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryEndpointCofData.jsonData 5842
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7])
    :
    recovered_closed_result_type%
      DaggerRecoveredUnitaryEndpointCofData.jsonData 5842
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredUnitaryEndpointCofData.jsonData 5842 :=
    @(recovered_closed_expr%
      DaggerRecoveredUnitaryEndpointCofData.jsonData 5987)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5 arg6 arg7 arg8

theorem DaggerUnitaryEndpointCof.returnSquareLift._proof_1.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryEndpointCofData.jsonData 2754 :=
  @(recovered_closed_expr%
    DaggerRecoveredUnitaryEndpointCofData.jsonData 2874)

theorem DaggerUnitaryEndpointCof.returnSquareLift._proof_2.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryEndpointCofData.jsonData 7021 :=
  @(recovered_closed_expr%
    DaggerRecoveredUnitaryEndpointCofData.jsonData 7559)

noncomputable def DaggerUnitaryEndpointCof.returnSquareLift.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryEndpointCofData.jsonData 7759
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryEndpointCofData.jsonData 7759
        [arg0]}
    {arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryEndpointCofData.jsonData 7759
        [arg0, arg1]}
    {arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryEndpointCofData.jsonData 7759
        [arg0, arg1, arg2]}
    {arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryEndpointCofData.jsonData 7759
        [arg0, arg1, arg2, arg3]}
    {arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryEndpointCofData.jsonData 7759
        [arg0, arg1, arg2, arg3, arg4]}
    {arg6 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryEndpointCofData.jsonData 7759
        [arg0, arg1, arg2, arg3, arg4, arg5]}
    (arg7 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryEndpointCofData.jsonData 7759
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6])
    (arg8 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryEndpointCofData.jsonData 7759
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7])
    (arg9 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryEndpointCofData.jsonData 7759
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8])
    :
    recovered_closed_result_type%
      DaggerRecoveredUnitaryEndpointCofData.jsonData 7759
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredUnitaryEndpointCofData.jsonData 7759 :=
    @(recovered_closed_expr%
      DaggerRecoveredUnitaryEndpointCofData.jsonData 7830)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5 arg6 arg7 arg8 arg9

theorem DaggerUnitaryEndpointCof.endpointData._proof_1.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryEndpointCofData.jsonData 7694 :=
  @(recovered_closed_expr%
    DaggerRecoveredUnitaryEndpointCofData.jsonData 7701)

theorem DaggerUnitaryEndpointCof.pointSquare_object.{u} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryEndpointCofData.jsonData 935 :=
  @(recovered_closed_expr%
    DaggerRecoveredUnitaryEndpointCofData.jsonData 980)

theorem DaggerUnitaryEndpointCof.endpointData._proof_2.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryEndpointCofData.jsonData 2125 :=
  @(recovered_closed_expr%
    DaggerRecoveredUnitaryEndpointCofData.jsonData 2145)

theorem DaggerUnitaryEndpointCof.endpointData._proof_3.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryEndpointCofData.jsonData 2174 :=
  @(recovered_closed_expr%
    DaggerRecoveredUnitaryEndpointCofData.jsonData 2184)

theorem DaggerUnitaryEndpointCof.endpointData._proof_4.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryEndpointCofData.jsonData 7725 :=
  @(recovered_closed_expr%
    DaggerRecoveredUnitaryEndpointCofData.jsonData 7738)

theorem DaggerUnitaryEndpointCof.endpointData._proof_5.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryEndpointCofData.jsonData 7684 :=
  @(recovered_closed_expr%
    DaggerRecoveredUnitaryEndpointCofData.jsonData 7690)

theorem DaggerUnitaryEndpointCof.endpointData._proof_6.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryEndpointCofData.jsonData 3155 :=
  @(recovered_closed_expr%
    DaggerRecoveredUnitaryEndpointCofData.jsonData 3164)

theorem DaggerUnitaryEndpointCof.endpointData._proof_7.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryEndpointCofData.jsonData 5754 :=
  @(recovered_closed_expr%
    DaggerRecoveredUnitaryEndpointCofData.jsonData 5772)

noncomputable def DaggerUnitaryEndpointCof.endpointData.{u}
    (arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryEndpointCofData.jsonData 6675
        [])
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryEndpointCofData.jsonData 6675
        [arg0]}
    {arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryEndpointCofData.jsonData 6675
        [arg0, arg1]}
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryEndpointCofData.jsonData 6675
        [arg0, arg1, arg2])
    (arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryEndpointCofData.jsonData 6675
        [arg0, arg1, arg2, arg3])
    (arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryEndpointCofData.jsonData 6675
        [arg0, arg1, arg2, arg3, arg4])
    (arg6 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryEndpointCofData.jsonData 6675
        [arg0, arg1, arg2, arg3, arg4, arg5])
    (arg7 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryEndpointCofData.jsonData 6675
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6])
    (arg8 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryEndpointCofData.jsonData 6675
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7])
    :
    recovered_closed_result_type%
      DaggerRecoveredUnitaryEndpointCofData.jsonData 6675
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredUnitaryEndpointCofData.jsonData 6675 :=
    @(recovered_closed_expr%
      DaggerRecoveredUnitaryEndpointCofData.jsonData 6932)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5 arg6 arg7 arg8

noncomputable def DaggerUnitaryEndpointCof.originalSquareLift.{u}
    (arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryEndpointCofData.jsonData 8009
        [])
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryEndpointCofData.jsonData 8009
        [arg0]}
    {arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryEndpointCofData.jsonData 8009
        [arg0, arg1]}
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryEndpointCofData.jsonData 8009
        [arg0, arg1, arg2])
    (arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryEndpointCofData.jsonData 8009
        [arg0, arg1, arg2, arg3])
    (arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryEndpointCofData.jsonData 8009
        [arg0, arg1, arg2, arg3, arg4])
    (arg6 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryEndpointCofData.jsonData 8009
        [arg0, arg1, arg2, arg3, arg4, arg5])
    (arg7 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryEndpointCofData.jsonData 8009
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6])
    (arg8 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryEndpointCofData.jsonData 8009
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7])
    :
    recovered_closed_result_type%
      DaggerRecoveredUnitaryEndpointCofData.jsonData 8009
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredUnitaryEndpointCofData.jsonData 8009 :=
    @(recovered_closed_expr%
      DaggerRecoveredUnitaryEndpointCofData.jsonData 8038)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5 arg6 arg7 arg8

theorem DaggerUnitaryEndpointCof.endpoint_hasLiftingProperty.{u} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryEndpointCofData.jsonData 4257 :=
  @(recovered_closed_expr%
    DaggerRecoveredUnitaryEndpointCofData.jsonData 4309)

theorem DaggerUnitaryEndpointCof.endpoint_cof.{u} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryEndpointCofData.jsonData 7856 :=
  @(recovered_closed_expr%
    DaggerRecoveredUnitaryEndpointCofData.jsonData 7872)

theorem DaggerUnitaryEndpointCof.endpoint_cellRetracts.{u} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryEndpointCofData.jsonData 6630 :=
  @(recovered_closed_expr%
    DaggerRecoveredUnitaryEndpointCofData.jsonData 6662)

theorem DaggerUnitaryEndpointCof.both_endpoint_cellRetracts.{u} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryEndpointCofData.jsonData 271 :=
  @(recovered_closed_expr%
    DaggerRecoveredUnitaryEndpointCofData.jsonData 281)

theorem DaggerUnitaryEndpointCof.returnSquareLift_obj.{u} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryEndpointCofData.jsonData 389 :=
  @(recovered_closed_expr%
    DaggerRecoveredUnitaryEndpointCofData.jsonData 600)

noncomputable def DaggerUnitaryEndpointCof.liftHomEndpointEq.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryEndpointCofData.jsonData 871
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryEndpointCofData.jsonData 871
        [arg0]}
    {arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryEndpointCofData.jsonData 871
        [arg0, arg1]}
    {arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryEndpointCofData.jsonData 871
        [arg0, arg1, arg2]}
    (arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryEndpointCofData.jsonData 871
        [arg0, arg1, arg2, arg3])
    (arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryEndpointCofData.jsonData 871
        [arg0, arg1, arg2, arg3, arg4])
    (arg6 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryEndpointCofData.jsonData 871
        [arg0, arg1, arg2, arg3, arg4, arg5])
    (arg7 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryEndpointCofData.jsonData 871
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6])
    :
    recovered_closed_result_type%
      DaggerRecoveredUnitaryEndpointCofData.jsonData 871
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredUnitaryEndpointCofData.jsonData 871 :=
    @(recovered_closed_expr%
      DaggerRecoveredUnitaryEndpointCofData.jsonData 899)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5 arg6 arg7

noncomputable def DaggerUnitaryEndpointCof.liftHomRawEndpointEq.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryEndpointCofData.jsonData 2514
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryEndpointCofData.jsonData 2514
        [arg0]}
    {arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryEndpointCofData.jsonData 2514
        [arg0, arg1]}
    {arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryEndpointCofData.jsonData 2514
        [arg0, arg1, arg2]}
    (arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryEndpointCofData.jsonData 2514
        [arg0, arg1, arg2, arg3])
    (arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryEndpointCofData.jsonData 2514
        [arg0, arg1, arg2, arg3, arg4])
    (arg6 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryEndpointCofData.jsonData 2514
        [arg0, arg1, arg2, arg3, arg4, arg5])
    (arg7 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryEndpointCofData.jsonData 2514
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6])
    :
    recovered_closed_result_type%
      DaggerRecoveredUnitaryEndpointCofData.jsonData 2514
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredUnitaryEndpointCofData.jsonData 2514 :=
    @(recovered_closed_expr%
      DaggerRecoveredUnitaryEndpointCofData.jsonData 2560)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5 arg6 arg7

theorem DaggerUnitaryEndpointCof.liftHom_raw_forward.{u} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryEndpointCofData.jsonData 1107 :=
  @(recovered_closed_expr%
    DaggerRecoveredUnitaryEndpointCofData.jsonData 1565)

theorem DaggerUnitaryEndpointCof.returnSquareLift_map.{u} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryEndpointCofData.jsonData 2013 :=
  @(recovered_closed_expr%
    DaggerRecoveredUnitaryEndpointCofData.jsonData 2028)

theorem DaggerUnitaryEndpointCof.right_cof.{u} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryEndpointCofData.jsonData 2568 :=
  @(recovered_closed_expr%
    DaggerRecoveredUnitaryEndpointCofData.jsonData 2572)

theorem DaggerUnitaryEndpointCof.left_cof.{u} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryEndpointCofData.jsonData 3055 :=
  @(recovered_closed_expr%
    DaggerRecoveredUnitaryEndpointCofData.jsonData 3057)

theorem DaggerUnitaryEndpointCof.liftHom_evaluated_forward.{u} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryEndpointCofData.jsonData 3932 :=
  @(recovered_closed_expr%
    DaggerRecoveredUnitaryEndpointCofData.jsonData 4070)

theorem DaggerUnitaryEndpointCof.returnSquareLift_functor.{u} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryEndpointCofData.jsonData 4759 :=
  @(recovered_closed_expr%
    DaggerRecoveredUnitaryEndpointCofData.jsonData 4771)

theorem DaggerUnitaryEndpointCof.liftHom_evaluated_backward.{u} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryEndpointCofData.jsonData 6010 :=
  @(recovered_closed_expr%
    DaggerRecoveredUnitaryEndpointCofData.jsonData 6091)

theorem DaggerUnitaryEndpointCof.originalSquareLift_selected.{u} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryEndpointCofData.jsonData 7633 :=
  @(recovered_closed_expr%
    DaggerRecoveredUnitaryEndpointCofData.jsonData 7670)

theorem DaggerUnitaryEndpointCof.liftHom_raw_backward.{u} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryEndpointCofData.jsonData 7928 :=
  @(recovered_closed_expr%
    DaggerRecoveredUnitaryEndpointCofData.jsonData 7992)

