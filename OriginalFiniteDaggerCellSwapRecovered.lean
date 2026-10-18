import DaggerModels.TwoObjectDaggerCell
import DaggerModels.FreeSimplicialMap
import OriginalRecoveredClosedExpressionApplication
import OriginalRecoveredFinitePrivateExpression
import OriginalRecoveredFiniteRelativeCellFoundationData

/-! Original FiniteDaggerCellSwap, with unchanged closed types and values. -/

set_option autoImplicit false
set_option maxRecDepth 100000

noncomputable def DaggerFiniteDaggerExtension.flipVertex.{u}
    (arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 1453
        [])
    :
    recovered_closed_result_type%
      DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 1453
      [arg0]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 1453 :=
    @(recovered_finite_private_expr%
      DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 1460)
  exact @f arg0

noncomputable abbrev DaggerFiniteDaggerExtension.graphSwapMap.match_1.{u_1, u_2}
    (arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 3665
        [])
    (arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 3665
        [arg0])
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 3665
        [arg0, arg1])
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 3665
        [arg0, arg1, arg2])
    (arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 3665
        [arg0, arg1, arg2, arg3])
    (arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 3665
        [arg0, arg1, arg2, arg3, arg4])
    (arg6 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 3665
        [arg0, arg1, arg2, arg3, arg4, arg5])
    (arg7 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 3665
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6])
    :
    recovered_closed_result_type%
      DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 3665
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 3665 :=
    @(recovered_finite_private_expr%
      DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 3723)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5 arg6 arg7

theorem DaggerFiniteDaggerExtension.graphSwapMap._proof_1.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 1591 :=
  @(recovered_finite_private_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 2203)

noncomputable def DaggerFiniteDaggerExtension.graphSwapMap.{u}
    (arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 2415
        [])
    :
    recovered_closed_result_type%
      DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 2415
      [arg0]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 2415 :=
    @(recovered_finite_private_expr%
      DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 2465)
  exact @f arg0

theorem DaggerFiniteDaggerExtension.graphSwapMap_comp.{u} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 66 :=
  @(recovered_finite_private_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 1233)

noncomputable def DaggerFiniteDaggerExtension.graphSwap.{u}
    (arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 1465
        [])
    :
    recovered_closed_result_type%
      DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 1465
      [arg0]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 1465 :=
    @(recovered_finite_private_expr%
      DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 1477)
  exact @f arg0

noncomputable def DaggerFiniteDaggerExtension.cellSwap.{u}
    (arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 2326
        [])
    :
    recovered_closed_result_type%
      DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 2326
      [arg0]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 2326 :=
    @(recovered_finite_private_expr%
      DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 2327)
  exact @f arg0

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteDaggerExtension.cellSwap.eq_1)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerModels.TwoObjectDaggerCell.functor.eq_1)
  pure ()

theorem DaggerFiniteDaggerExtension.cellSwap_naturality._simp_1_3.{v₁, v₂, u₁, u₂} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 2299 :=
  @(recovered_finite_private_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 2325)

theorem DaggerFiniteDaggerExtension.graphSwap_naturality.{u} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 2471 :=
  @(recovered_finite_private_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 3549)

theorem DaggerFiniteDaggerExtension.cellSwap_naturality.{u} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 1312 :=
  @(recovered_finite_private_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 1451)

theorem DaggerFiniteDaggerExtension.flipVertex_involutive.{u} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 2331 :=
  @(recovered_finite_private_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 2375)

theorem DaggerFiniteDaggerExtension.cellSwap_obj.{u} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 2410 :=
  @(recovered_finite_private_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 2414)

theorem DaggerFiniteDaggerExtension.cellSwap_path.{u} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 3627 :=
  @(recovered_finite_private_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 3640)

