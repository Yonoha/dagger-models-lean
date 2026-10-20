import PointCoproductCore
import OriginalDKEndpointTransportRecovered
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
import OriginalRecoveredClosedExpressionApplication
import OriginalRecoveredGlobalLeftProperData

/-! Original PointCoproductUP, with unchanged closed types and values. -/

set_option autoImplicit false
set_option maxRecDepth 100000

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerGlobalDKClosure.transport.eq_1)
  pure ()

noncomputable def DaggerPointCoproduct.descObj.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 22032
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 22032
        [arg0]}
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 22032
        [arg0, arg1])
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 22032
        [arg0, arg1, arg2])
    :
    recovered_closed_result_type%
      DaggerRecoveredGlobalLeftProperData.jsonData 22032
      [arg0, arg1, arg2, arg3]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 22032 :=
    @(recovered_closed_expr%
      DaggerRecoveredGlobalLeftProperData.jsonData 22036)
  exact @f arg0 arg1 arg2 arg3

theorem DaggerPointCoproduct.descMap._proof_1.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 25042 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 25048)

theorem DaggerPointCoproduct.descMap._proof_2.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 24496 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 24556)

theorem DaggerPointCoproduct.descMap._proof_3.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 24593 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 24601)

theorem DaggerPointCoproduct.descMap._proof_4.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 25054 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 25058)

theorem DaggerPointCoproduct.descMap._proof_5.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 21928 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 21989)

noncomputable def DaggerPointCoproduct.descMap.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 22555
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 22555
        [arg0]}
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 22555
        [arg0, arg1])
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 22555
        [arg0, arg1, arg2])
    (arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 22555
        [arg0, arg1, arg2, arg3])
    (arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 22555
        [arg0, arg1, arg2, arg3, arg4])
    :
    recovered_closed_result_type%
      DaggerRecoveredGlobalLeftProperData.jsonData 22555
      [arg0, arg1, arg2, arg3, arg4, arg5]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 22555 :=
    @(recovered_closed_expr%
      DaggerRecoveredGlobalLeftProperData.jsonData 22862)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5

theorem DaggerPointCoproduct.desc._proof_1.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 24849 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 24964)

theorem DaggerPointCoproduct.desc._proof_2.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 19534 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 20894)

theorem DaggerPointCoproduct.desc._proof_3.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 21287 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 21683)

noncomputable def DaggerPointCoproduct.desc.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 24607
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 24607
        [arg0]}
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 24607
        [arg0, arg1])
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 24607
        [arg0, arg1, arg2])
    :
    recovered_closed_result_type%
      DaggerRecoveredGlobalLeftProperData.jsonData 24607
      [arg0, arg1, arg2, arg3]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 24607 :=
    @(recovered_closed_expr%
      DaggerRecoveredGlobalLeftProperData.jsonData 24644)
  exact @f arg0 arg1 arg2 arg3

theorem DaggerPointCoproduct.inPoint_desc.{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 19274 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 19426)

theorem DaggerPointCoproduct.apexIso._proof_1.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 25010 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 25015)

theorem DaggerPointCoproduct.hom_ext.{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 22883 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 24090)

theorem DaggerPointCoproduct.apexIso._simp_1.{v, u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 24280 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 24302)

theorem DaggerPointCoproduct.inOld_desc.{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 22339 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 22436)

theorem DaggerPointCoproduct.apexIso._proof_2.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 20957 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 21225)

theorem DaggerPointCoproduct.apexIso._proof_3.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 21698 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 21852)

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerPointCoproduct.descObj.eq_1)
  pure ()

theorem DaggerPointCoproduct.desc_restrict.{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 22446 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 22516)

theorem DaggerPointCoproduct.homEquiv._proof_1.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 24338 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 24437)

noncomputable def DaggerPointCoproduct.homEquiv.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 22048
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 22048
        [arg0]}
    :
    recovered_closed_result_type%
      DaggerRecoveredGlobalLeftProperData.jsonData 22048
      [arg0, arg1]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 22048 :=
    @(recovered_closed_expr%
      DaggerRecoveredGlobalLeftProperData.jsonData 22095)
  exact @f arg0 arg1

theorem DaggerPointCoproduct.isColimit._proof_2.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 22142 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 22148)

theorem DaggerPointCoproduct.isColimit._proof_3.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 22207 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 22326)

theorem DaggerPointCoproduct.isColimit._proof_1.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 22528 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 22534)

noncomputable def DaggerPointCoproduct.apexIso.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 24651
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 24651
        [arg0]}
    {arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 24651
        [arg0, arg1]}
    {arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 24651
        [arg0, arg1, arg2]}
    (arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 24651
        [arg0, arg1, arg2, arg3])
    :
    recovered_closed_result_type%
      DaggerRecoveredGlobalLeftProperData.jsonData 24651
      [arg0, arg1, arg2, arg3, arg4]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 24651 :=
    @(recovered_closed_expr%
      DaggerRecoveredGlobalLeftProperData.jsonData 24693)
  exact @f arg0 arg1 arg2 arg3 arg4

theorem DaggerPointCoproduct.apexIso_old.{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 24122 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 24131)

theorem DaggerPointCoproduct.point_apexIso_inv.{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 24147 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 24171)

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerPointCoproduct.inOld.eq_1)
  pure ()

theorem DaggerPointCoproduct.apexIso_point.{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 24564 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 24573)

theorem DaggerPointCoproduct.old_apexIso_inv.{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 24706 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 24727)

noncomputable def DaggerPointCoproduct.isColimit.{u}
    (arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 24749
        [])
    :
    recovered_closed_result_type%
      DaggerRecoveredGlobalLeftProperData.jsonData 24749
      [arg0]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 24749 :=
    @(recovered_closed_expr%
      DaggerRecoveredGlobalLeftProperData.jsonData 24799)
  exact @f arg0

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerPointCoproduct.inPoint.eq_1)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerPointCoproduct.desc.eq_1)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerPointCoproduct.descMap.eq_1)
  pure ()

