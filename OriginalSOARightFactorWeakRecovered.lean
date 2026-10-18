import OriginalSOARightFactorRecovered
import OriginalGlobalModelDataRecovered
import OriginalRecoveredClosedExpressionApplication
import OriginalRecoveredActualWeakPipelineData

/-! Original SOARightFactorWeak, with unchanged closed types and values. -/

set_option autoImplicit false
set_option maxRecDepth 100000

theorem DaggerSOAAccessible.originalWeakIffRightFactor.{u} :
  recovered_closed_expr%
    DaggerRecoveredActualWeakPipelineData.jsonData 883 :=
  @(recovered_closed_expr%
    DaggerRecoveredActualWeakPipelineData.jsonData 1229)

theorem DaggerSOAAccessible.originalWeakArrowPredicate.{u} :
  recovered_closed_expr%
    DaggerRecoveredActualWeakPipelineData.jsonData 1260 :=
  @(recovered_closed_expr%
    DaggerRecoveredActualWeakPipelineData.jsonData 1277)

