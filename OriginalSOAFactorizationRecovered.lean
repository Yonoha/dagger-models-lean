import OriginalSOAStepRecovered
import OriginalSOAUniformRankRecovered
import OriginalSOARightFactorRecovered
import OriginalRecoveredClosedExpressionApplication
import OriginalRecoveredSOAAccessibilityData

/-! Original SOAFactorization, with unchanged closed types and values. -/

set_option autoImplicit false
set_option maxRecDepth 100000

noncomputable abbrev DaggerSOAStepAccessible.factorization.{w, v, u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredSOAAccessibilityData.jsonData 45937
        []}
    [arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredSOAAccessibilityData.jsonData 45937
        [arg0]]
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredSOAAccessibilityData.jsonData 45937
        [arg0, arg1])
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredSOAAccessibilityData.jsonData 45937
        [arg0, arg1, arg2])
    [arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredSOAAccessibilityData.jsonData 45937
        [arg0, arg1, arg2, arg3]]
    [arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredSOAAccessibilityData.jsonData 45937
        [arg0, arg1, arg2, arg3, arg4]]
    [arg6 :
      recovered_closed_binder_type%
        DaggerRecoveredSOAAccessibilityData.jsonData 45937
        [arg0, arg1, arg2, arg3, arg4, arg5]]
    :
    recovered_closed_result_type%
      DaggerRecoveredSOAAccessibilityData.jsonData 45937
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredSOAAccessibilityData.jsonData 45937 :=
    @(recovered_closed_expr%
      DaggerRecoveredSOAAccessibilityData.jsonData 45944)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5 arg6

theorem DaggerSOAStepAccessible.factorization_fac.{w, v, u} :
  recovered_closed_expr%
    DaggerRecoveredSOAAccessibilityData.jsonData 46127 :=
  @(recovered_closed_expr%
    DaggerRecoveredSOAAccessibilityData.jsonData 46142)

theorem DaggerSOAStepAccessible.factorization_fac_assoc.{w, v, u} :
  recovered_closed_expr%
    DaggerRecoveredSOAAccessibilityData.jsonData 45633 :=
  @(recovered_closed_expr%
    DaggerRecoveredSOAAccessibilityData.jsonData 45756)

theorem DaggerSOAStepAccessible.factorization_p.{w, v, u} :
  recovered_closed_expr%
    DaggerRecoveredSOAAccessibilityData.jsonData 45769 :=
  @(recovered_closed_expr%
    DaggerRecoveredSOAAccessibilityData.jsonData 45779)

theorem DaggerSOAStepAccessible.factorization_obj.{w, v, u} :
  recovered_closed_expr%
    DaggerRecoveredSOAAccessibilityData.jsonData 45789 :=
  @(recovered_closed_expr%
    DaggerRecoveredSOAAccessibilityData.jsonData 45798)

theorem DaggerSOAStepAccessible.property_step_accessible.{w, v, u} :
  recovered_closed_expr%
    DaggerRecoveredSOAAccessibilityData.jsonData 45969 :=
  @(recovered_closed_expr%
    DaggerRecoveredSOAAccessibilityData.jsonData 46082)

theorem DaggerSOAStepAccessible.property_rightFactor_accessible.{w, v, u} :
  recovered_closed_expr%
    DaggerRecoveredSOAAccessibilityData.jsonData 46178 :=
  @(recovered_closed_expr%
    DaggerRecoveredSOAAccessibilityData.jsonData 46213)

theorem DaggerSOAStepAccessible.factorization_Z_accessible.{w, v, u} :
  recovered_closed_expr%
    DaggerRecoveredSOAAccessibilityData.jsonData 45839 :=
  @(recovered_closed_expr%
    DaggerRecoveredSOAAccessibilityData.jsonData 45930)

theorem DaggerSOAStepAccessible.factorization_map.{w, v, u} :
  recovered_closed_expr%
    DaggerRecoveredSOAAccessibilityData.jsonData 46102 :=
  @(recovered_closed_expr%
    DaggerRecoveredSOAAccessibilityData.jsonData 46114)

theorem DaggerSOAStepAccessible.factorization_i.{w, v, u} :
  recovered_closed_expr%
    DaggerRecoveredSOAAccessibilityData.jsonData 46154 :=
  @(recovered_closed_expr%
    DaggerRecoveredSOAAccessibilityData.jsonData 46164)

noncomputable def DaggerSOAStepAccessible.factorization_cell.{w, v, u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredSOAAccessibilityData.jsonData 46246
        []}
    [arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredSOAAccessibilityData.jsonData 46246
        [arg0]]
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredSOAAccessibilityData.jsonData 46246
        [arg0, arg1])
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredSOAAccessibilityData.jsonData 46246
        [arg0, arg1, arg2])
    [arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredSOAAccessibilityData.jsonData 46246
        [arg0, arg1, arg2, arg3]]
    [arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredSOAAccessibilityData.jsonData 46246
        [arg0, arg1, arg2, arg3, arg4]]
    [arg6 :
      recovered_closed_binder_type%
        DaggerRecoveredSOAAccessibilityData.jsonData 46246
        [arg0, arg1, arg2, arg3, arg4, arg5]]
    (arg7 :
      recovered_closed_binder_type%
        DaggerRecoveredSOAAccessibilityData.jsonData 46246
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6])
    :
    recovered_closed_result_type%
      DaggerRecoveredSOAAccessibilityData.jsonData 46246
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredSOAAccessibilityData.jsonData 46246 :=
    @(recovered_closed_expr%
      DaggerRecoveredSOAAccessibilityData.jsonData 46265)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5 arg6 arg7

theorem DaggerSOAStepAccessible.factorization_naturality.{w, v, u} :
  recovered_closed_expr%
    DaggerRecoveredSOAAccessibilityData.jsonData 46325 :=
  @(recovered_closed_expr%
    DaggerRecoveredSOAAccessibilityData.jsonData 46370)

