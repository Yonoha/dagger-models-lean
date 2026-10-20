import OriginalUnitaryRealizationPullbackRecovered
import OriginalRecoveredClosedExpressionApplication
import OriginalRecoveredUnitaryRealizationPreparationData

/-! Original UnitaryRealizationAmbient, with unchanged closed types and values. -/

set_option autoImplicit false
set_option maxRecDepth 100000

noncomputable def DaggerUnitaryRealization.ambient.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryRealizationPreparationData.jsonData 6275
        []}
    (arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryRealizationPreparationData.jsonData 6275
        [arg0])
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryRealizationPreparationData.jsonData 6275
        [arg0, arg1])
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryRealizationPreparationData.jsonData 6275
        [arg0, arg1, arg2])
    (arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryRealizationPreparationData.jsonData 6275
        [arg0, arg1, arg2, arg3])
    :
    recovered_closed_result_type%
      DaggerRecoveredUnitaryRealizationPreparationData.jsonData 6275
      [arg0, arg1, arg2, arg3, arg4]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredUnitaryRealizationPreparationData.jsonData 6275 :=
    @(recovered_closed_expr%
      DaggerRecoveredUnitaryRealizationPreparationData.jsonData 6303)
  exact @f arg0 arg1 arg2 arg3 arg4

theorem DaggerUnitaryRealization.ambient_obj.{u} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryRealizationPreparationData.jsonData 6145 :=
  @(recovered_closed_expr%
    DaggerRecoveredUnitaryRealizationPreparationData.jsonData 6254)

theorem DaggerUnitaryRealization.ambient_left.{u} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryRealizationPreparationData.jsonData 6113 :=
  @(recovered_closed_expr%
    DaggerRecoveredUnitaryRealizationPreparationData.jsonData 6136)

theorem DaggerUnitaryRealization.ambient_right.{u} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryRealizationPreparationData.jsonData 6262 :=
  @(recovered_closed_expr%
    DaggerRecoveredUnitaryRealizationPreparationData.jsonData 6268)

theorem DaggerUnitaryRealization.ambient_map.{u} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryRealizationPreparationData.jsonData 6383 :=
  @(recovered_closed_expr%
    DaggerRecoveredUnitaryRealizationPreparationData.jsonData 8159)

theorem DaggerUnitaryRealization.ambient_J.{u} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryRealizationPreparationData.jsonData 8236 :=
  @(recovered_closed_expr%
    DaggerRecoveredUnitaryRealizationPreparationData.jsonData 8331)

theorem DaggerUnitaryRealization.ambient_generator.{u} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryRealizationPreparationData.jsonData 8384 :=
  @(recovered_closed_expr%
    DaggerRecoveredUnitaryRealizationPreparationData.jsonData 8562)

