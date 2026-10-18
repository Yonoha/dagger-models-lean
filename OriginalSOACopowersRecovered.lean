import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.ShrinkYoneda
import OriginalRecoveredClosedExpressionApplication
import OriginalRecoveredSOAAccessibilityData

/-! Original SOACopowers, with unchanged closed types and values. -/

set_option autoImplicit false
set_option maxRecDepth 100000

theorem DaggerSOAStepAccessible.coyoneda_small.{w, v, u} :
  recovered_closed_expr%
    DaggerRecoveredSOAAccessibilityData.jsonData 2269 :=
  @(recovered_closed_expr%
    DaggerRecoveredSOAAccessibilityData.jsonData 2304)
attribute [instance] DaggerSOAStepAccessible.coyoneda_small

theorem DaggerSOAStepAccessible.copowerHomEquiv._proof_1.{u_1, u_2, u_3} :
  recovered_closed_expr%
    DaggerRecoveredSOAAccessibilityData.jsonData 4060 :=
  @(recovered_closed_expr%
    DaggerRecoveredSOAAccessibilityData.jsonData 4071)

theorem DaggerSOAStepAccessible.copowerHomEquiv._proof_2.{u_1, u_2, u_3} :
  recovered_closed_expr%
    DaggerRecoveredSOAAccessibilityData.jsonData 282 :=
  @(recovered_closed_expr%
    DaggerRecoveredSOAAccessibilityData.jsonData 716)

theorem DaggerSOAStepAccessible.copowerHomEquiv._proof_3.{u_1, u_2, u_3} :
  recovered_closed_expr%
    DaggerRecoveredSOAAccessibilityData.jsonData 988 :=
  @(recovered_closed_expr%
    DaggerRecoveredSOAAccessibilityData.jsonData 1351)

noncomputable def DaggerSOAStepAccessible.copowerHomEquiv.{w, v, u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredSOAAccessibilityData.jsonData 5427
        []}
    [arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredSOAAccessibilityData.jsonData 5427
        [arg0]]
    [arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredSOAAccessibilityData.jsonData 5427
        [arg0, arg1]]
    [arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredSOAAccessibilityData.jsonData 5427
        [arg0, arg1, arg2]]
    (arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredSOAAccessibilityData.jsonData 5427
        [arg0, arg1, arg2, arg3])
    (arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredSOAAccessibilityData.jsonData 5427
        [arg0, arg1, arg2, arg3, arg4])
    (arg6 :
      recovered_closed_binder_type%
        DaggerRecoveredSOAAccessibilityData.jsonData 5427
        [arg0, arg1, arg2, arg3, arg4, arg5])
    :
    recovered_closed_result_type%
      DaggerRecoveredSOAAccessibilityData.jsonData 5427
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredSOAAccessibilityData.jsonData 5427 :=
    @(recovered_closed_expr%
      DaggerRecoveredSOAAccessibilityData.jsonData 5434)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5 arg6

theorem DaggerSOAStepAccessible.smallSigmaConstAdj._proof_1.{u_1, u_2, u_3} :
  recovered_closed_expr%
    DaggerRecoveredSOAAccessibilityData.jsonData 4392 :=
  @(recovered_closed_expr%
    DaggerRecoveredSOAAccessibilityData.jsonData 4811)

theorem DaggerSOAStepAccessible.smallSigmaConstAdj._proof_2.{u_1, u_2, u_3} :
  recovered_closed_expr%
    DaggerRecoveredSOAAccessibilityData.jsonData 5523 :=
  @(recovered_closed_expr%
    DaggerRecoveredSOAAccessibilityData.jsonData 5803)

noncomputable def DaggerSOAStepAccessible.smallSigmaConstAdj.{w, v, u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredSOAAccessibilityData.jsonData 2208
        []}
    [arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredSOAAccessibilityData.jsonData 2208
        [arg0]]
    [arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredSOAAccessibilityData.jsonData 2208
        [arg0, arg1]]
    [arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredSOAAccessibilityData.jsonData 2208
        [arg0, arg1, arg2]]
    (arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredSOAAccessibilityData.jsonData 2208
        [arg0, arg1, arg2, arg3])
    :
    recovered_closed_result_type%
      DaggerRecoveredSOAAccessibilityData.jsonData 2208
      [arg0, arg1, arg2, arg3, arg4]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredSOAAccessibilityData.jsonData 2208 :=
    @(recovered_closed_expr%
      DaggerRecoveredSOAAccessibilityData.jsonData 2240)
  exact @f arg0 arg1 arg2 arg3 arg4

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerSOAStepAccessible.smallSigmaConstAdj.eq_1)
  pure ()

theorem DaggerSOAStepAccessible.smallSigmaConstAdj_homEquiv_symm.{w, v, u} :
  recovered_closed_expr%
    DaggerRecoveredSOAAccessibilityData.jsonData 1652 :=
  @(recovered_closed_expr%
    DaggerRecoveredSOAAccessibilityData.jsonData 1974)

theorem DaggerSOAStepAccessible.smallSigmaConstAdj_counit.{w, v, u} :
  recovered_closed_expr%
    DaggerRecoveredSOAAccessibilityData.jsonData 2146 :=
  @(recovered_closed_expr%
    DaggerRecoveredSOAAccessibilityData.jsonData 2155)

theorem DaggerSOAStepAccessible.smallSigmaConstAdj_unit.{w, v, u} :
  recovered_closed_expr%
    DaggerRecoveredSOAAccessibilityData.jsonData 2436 :=
  @(recovered_closed_expr%
    DaggerRecoveredSOAAccessibilityData.jsonData 4011)

theorem DaggerSOAStepAccessible.sigmaConst_preservesSmallColimits.{w, v, u} :
  recovered_closed_expr%
    DaggerRecoveredSOAAccessibilityData.jsonData 4022 :=
  @(recovered_closed_expr%
    DaggerRecoveredSOAAccessibilityData.jsonData 4040)

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `CategoryTheory.FunctorToTypes.shrink.eq_1)
  pure ()

theorem DaggerSOAStepAccessible.smallSigmaConstAdj_homEquiv_apply.{w, v, u} :
  recovered_closed_expr%
    DaggerRecoveredSOAAccessibilityData.jsonData 4905 :=
  @(recovered_closed_expr%
    DaggerRecoveredSOAAccessibilityData.jsonData 5109)

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerSOAStepAccessible.copowerHomEquiv.eq_1)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `CategoryTheory.Limits.sigmaConst.eq_1)
  pure ()

