import OriginalFiniteDaggerStageRecovered
import Mathlib.CategoryTheory.ComposableArrows.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Preorder.Fin
import OriginalRecoveredClosedExpressionApplication
import OriginalRecoveredFinitePrivateExpression
import OriginalRecoveredFiniteRelativeCellFoundationData

/-! Original FiniteDaggerChain, with unchanged closed types and values. -/

set_option autoImplicit false
set_option maxRecDepth 100000

noncomputable def DaggerFiniteDaggerExtension.stages.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 63255
        []}
    (arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 63255
        [arg0])
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 63255
        [arg0, arg1])
    {arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 63255
        [arg0, arg1, arg2]}
    {arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 63255
        [arg0, arg1, arg2, arg3]}
    (arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 63255
        [arg0, arg1, arg2, arg3, arg4])
    {arg6 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 63255
        [arg0, arg1, arg2, arg3, arg4, arg5]}
    {arg7 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 63255
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6]}
    [arg8 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 63255
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7]]
    (arg9 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 63255
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8])
    (arg10 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 63255
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9])
    (arg11 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 63255
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10])
    (arg12 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 63255
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11])
    :
    recovered_closed_result_type%
      DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 63255
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11, arg12]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 63255 :=
    @(recovered_finite_private_expr%
      DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 63316)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5 arg6 arg7 arg8 arg9 arg10 arg11 arg12

noncomputable def DaggerFiniteDaggerExtension.stageArrow.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 63731
        []}
    (arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 63731
        [arg0])
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 63731
        [arg0, arg1])
    {arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 63731
        [arg0, arg1, arg2]}
    {arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 63731
        [arg0, arg1, arg2, arg3]}
    (arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 63731
        [arg0, arg1, arg2, arg3, arg4])
    {arg6 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 63731
        [arg0, arg1, arg2, arg3, arg4, arg5]}
    {arg7 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 63731
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6]}
    [arg8 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 63731
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7]]
    (arg9 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 63731
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8])
    (arg10 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 63731
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9])
    (arg11 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 63731
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10])
    (arg12 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 63731
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11])
    :
    recovered_closed_result_type%
      DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 63731
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11, arg12]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 63731 :=
    @(recovered_finite_private_expr%
      DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 63756)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5 arg6 arg7 arg8 arg9 arg10 arg11 arg12

noncomputable def DaggerFiniteDaggerExtension.chain.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 62438
        []}
    (arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 62438
        [arg0])
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 62438
        [arg0, arg1])
    {arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 62438
        [arg0, arg1, arg2]}
    {arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 62438
        [arg0, arg1, arg2, arg3]}
    (arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 62438
        [arg0, arg1, arg2, arg3, arg4])
    {arg6 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 62438
        [arg0, arg1, arg2, arg3, arg4, arg5]}
    {arg7 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 62438
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6]}
    [arg8 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 62438
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7]]
    (arg9 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 62438
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8])
    (arg10 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 62438
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9])
    (arg11 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 62438
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10])
    :
    recovered_closed_result_type%
      DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 62438
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 62438 :=
    @(recovered_finite_private_expr%
      DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 62470)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5 arg6 arg7 arg8 arg9 arg10 arg11

theorem DaggerFiniteDaggerExtension.thetaNat._proof_2.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 62489 :=
  @(recovered_finite_private_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 62506)

theorem DaggerFiniteDaggerExtension.thetaNat._proof_3.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 62518 :=
  @(recovered_finite_private_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 62531)

theorem DaggerFiniteDaggerExtension.thetaNat._proof_4.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 61404 :=
  @(recovered_finite_private_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 61415)

theorem DaggerFiniteDaggerExtension.chain_succ.{u} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 63481 :=
  @(recovered_finite_private_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 63528)

theorem DaggerFiniteDaggerExtension.phiNat._proof_1.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 60037 :=
  @(recovered_finite_private_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 60454)

noncomputable abbrev DaggerFiniteDaggerExtension.finalObj.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 62900
        []}
    (arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 62900
        [arg0])
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 62900
        [arg0, arg1])
    {arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 62900
        [arg0, arg1, arg2]}
    {arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 62900
        [arg0, arg1, arg2, arg3]}
    (arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 62900
        [arg0, arg1, arg2, arg3, arg4])
    {arg6 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 62900
        [arg0, arg1, arg2, arg3, arg4, arg5]}
    {arg7 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 62900
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6]}
    [arg8 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 62900
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7]]
    (arg9 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 62900
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8])
    (arg10 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 62900
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9])
    (arg11 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 62900
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10])
    :
    recovered_closed_result_type%
      DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 62900
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 62900 :=
    @(recovered_finite_private_expr%
      DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 62912)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5 arg6 arg7 arg8 arg9 arg10 arg11

theorem DaggerFiniteDaggerExtension.theta._proof_1.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 62543 :=
  @(recovered_finite_private_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 62557)

noncomputable def DaggerFiniteDaggerExtension.theta.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 63799
        []}
    (arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 63799
        [arg0])
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 63799
        [arg0, arg1])
    {arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 63799
        [arg0, arg1, arg2]}
    {arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 63799
        [arg0, arg1, arg2, arg3]}
    (arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 63799
        [arg0, arg1, arg2, arg3, arg4])
    {arg6 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 63799
        [arg0, arg1, arg2, arg3, arg4, arg5]}
    {arg7 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 63799
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6]}
    [arg8 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 63799
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7]]
    (arg9 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 63799
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8])
    (arg10 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 63799
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9])
    (arg11 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 63799
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10])
    :
    recovered_closed_result_type%
      DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 63799
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 63799 :=
    @(recovered_finite_private_expr%
      DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 63811)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5 arg6 arg7 arg8 arg9 arg10 arg11

noncomputable def DaggerFiniteDaggerExtension.kappa.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 63769
        []}
    (arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 63769
        [arg0])
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 63769
        [arg0, arg1])
    {arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 63769
        [arg0, arg1, arg2]}
    {arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 63769
        [arg0, arg1, arg2, arg3]}
    (arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 63769
        [arg0, arg1, arg2, arg3, arg4])
    {arg6 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 63769
        [arg0, arg1, arg2, arg3, arg4, arg5]}
    {arg7 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 63769
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6]}
    [arg8 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 63769
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7]]
    (arg9 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 63769
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8])
    (arg10 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 63769
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9])
    (arg11 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 63769
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10])
    :
    recovered_closed_result_type%
      DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 63769
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 63769 :=
    @(recovered_finite_private_expr%
      DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 63786)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5 arg6 arg7 arg8 arg9 arg10 arg11

theorem DaggerFiniteDaggerExtension.thetaNat._proof_1.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 61379 :=
  @(recovered_finite_private_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 61393)

theorem DaggerFiniteDaggerExtension.thetaNat._proof_5.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 61673 :=
  @(recovered_finite_private_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 61902)

noncomputable def DaggerFiniteDaggerExtension.thetaNat.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 61464
        []}
    (arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 61464
        [arg0])
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 61464
        [arg0, arg1])
    {arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 61464
        [arg0, arg1, arg2]}
    {arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 61464
        [arg0, arg1, arg2, arg3]}
    (arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 61464
        [arg0, arg1, arg2, arg3, arg4])
    {arg6 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 61464
        [arg0, arg1, arg2, arg3, arg4, arg5]}
    {arg7 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 61464
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6]}
    [arg8 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 61464
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7]]
    (arg9 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 61464
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8])
    (arg10 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 61464
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9])
    (arg11 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 61464
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10])
    :
    recovered_closed_result_type%
      DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 61464
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 61464 :=
    @(recovered_finite_private_expr%
      DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 61515)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5 arg6 arg7 arg8 arg9 arg10 arg11

theorem DaggerFiniteDaggerExtension.theta_naturality.{u} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 63392 :=
  @(recovered_finite_private_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 63440)

theorem DaggerFiniteDaggerExtension.j_theta.{u} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 61919 :=
  @(recovered_finite_private_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 62422)

theorem DaggerFiniteDaggerExtension.j_theta_assoc.{u} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 60575 :=
  @(recovered_finite_private_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 60740)

noncomputable def DaggerFiniteDaggerExtension.finalCocone.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 60782
        []}
    (arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 60782
        [arg0])
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 60782
        [arg0, arg1])
    {arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 60782
        [arg0, arg1, arg2]}
    {arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 60782
        [arg0, arg1, arg2, arg3]}
    (arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 60782
        [arg0, arg1, arg2, arg3, arg4])
    {arg6 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 60782
        [arg0, arg1, arg2, arg3, arg4, arg5]}
    {arg7 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 60782
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6]}
    [arg8 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 60782
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7]]
    (arg9 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 60782
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8])
    (arg10 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 60782
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9])
    (arg11 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 60782
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10])
    :
    recovered_closed_result_type%
      DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 60782
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 60782 :=
    @(recovered_finite_private_expr%
      DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 60805)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5 arg6 arg7 arg8 arg9 arg10 arg11

theorem DaggerFiniteDaggerExtension.kappa_zero.{u} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 60842 :=
  @(recovered_finite_private_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 61180)

theorem DaggerFiniteDaggerExtension.stages_succ.{u} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 61235 :=
  @(recovered_finite_private_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 61250)

theorem DaggerFiniteDaggerExtension.chain_obj.{u} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 61297 :=
  @(recovered_finite_private_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 61312)

noncomputable def DaggerFiniteDaggerExtension.finalIsColimit.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 61343
        []}
    (arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 61343
        [arg0])
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 61343
        [arg0, arg1])
    {arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 61343
        [arg0, arg1, arg2]}
    {arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 61343
        [arg0, arg1, arg2, arg3]}
    (arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 61343
        [arg0, arg1, arg2, arg3, arg4])
    {arg6 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 61343
        [arg0, arg1, arg2, arg3, arg4, arg5]}
    {arg7 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 61343
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6]}
    [arg8 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 61343
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7]]
    (arg9 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 61343
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8])
    (arg10 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 61343
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9])
    (arg11 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 61343
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10])
    :
    recovered_closed_result_type%
      DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 61343
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 61343 :=
    @(recovered_finite_private_expr%
      DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 61363)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5 arg6 arg7 arg8 arg9 arg10 arg11

theorem DaggerFiniteDaggerExtension.stages_zero.{u} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 61571 :=
  @(recovered_finite_private_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 61585)

noncomputable def DaggerFiniteDaggerExtension.phiNat.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 62705
        []}
    (arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 62705
        [arg0])
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 62705
        [arg0, arg1])
    {arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 62705
        [arg0, arg1, arg2]}
    {arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 62705
        [arg0, arg1, arg2, arg3]}
    (arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 62705
        [arg0, arg1, arg2, arg3, arg4])
    {arg6 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 62705
        [arg0, arg1, arg2, arg3, arg4, arg5]}
    {arg7 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 62705
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6]}
    [arg8 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 62705
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7]]
    (arg9 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 62705
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8])
    (arg10 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 62705
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9])
    (arg11 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 62705
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10])
    :
    recovered_closed_result_type%
      DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 62705
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 62705 :=
    @(recovered_finite_private_expr%
      DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 62745)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5 arg6 arg7 arg8 arg9 arg10 arg11

theorem DaggerFiniteDaggerExtension.phi_naturality.{u} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 62618 :=
  @(recovered_finite_private_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 62673)

noncomputable def DaggerFiniteDaggerExtension.psi.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 63655
        []}
    (arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 63655
        [arg0])
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 63655
        [arg0, arg1])
    {arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 63655
        [arg0, arg1, arg2]}
    {arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 63655
        [arg0, arg1, arg2, arg3]}
    (arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 63655
        [arg0, arg1, arg2, arg3, arg4])
    {arg6 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 63655
        [arg0, arg1, arg2, arg3, arg4, arg5]}
    {arg7 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 63655
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6]}
    [arg8 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 63655
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7]]
    (arg9 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 63655
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8])
    (arg10 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 63655
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9])
    (arg11 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 63655
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10])
    :
    recovered_closed_result_type%
      DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 63655
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 63655 :=
    @(recovered_finite_private_expr%
      DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 63667)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5 arg6 arg7 arg8 arg9 arg10 arg11

theorem DaggerFiniteDaggerExtension.kappa_psi.{u} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 63684 :=
  @(recovered_finite_private_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 63712)

theorem DaggerFiniteDaggerExtension.kappa_psi_assoc.{u} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 62791 :=
  @(recovered_finite_private_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 62888)

theorem DaggerFiniteDaggerExtension.final_desc.{u} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 63001 :=
  @(recovered_finite_private_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 63016)

theorem DaggerFiniteDaggerExtension.theta_psi.{u} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 63039 :=
  @(recovered_finite_private_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 63241)

theorem DaggerFiniteDaggerExtension.theta_psi_assoc.{u} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 63566 :=
  @(recovered_finite_private_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 63641)

