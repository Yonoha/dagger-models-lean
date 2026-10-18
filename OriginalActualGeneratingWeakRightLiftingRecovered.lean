import OriginalActualAcyclicGeneratorPropertiesRecovered
import OriginalActualGlobalWeakPropertiesRecovered
import OriginalUnitaryEndpointCofRecovered
import OriginalRecoveredClosedExpressionApplication
import OriginalRecoveredActualGeneratingWeakRightLiftingData

/-! Original ActualGeneratingWeakRightLifting, with unchanged closed types and values. -/

set_option autoImplicit false
set_option maxRecDepth 100000

theorem DaggerGlobalJLifting.generators_rlp_le_J_rlp.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredActualGeneratingWeakRightLiftingData.jsonData 141 :=
  @(recovered_closed_expr%
    DaggerRecoveredActualGeneratingWeakRightLiftingData.jsonData 213)

theorem DaggerGlobalJLifting.generators_rlp_le_daggerDK_inter_J_rlp.{u} :
  recovered_closed_expr%
    DaggerRecoveredActualGeneratingWeakRightLiftingData.jsonData 72 :=
  @(recovered_closed_expr%
    DaggerRecoveredActualGeneratingWeakRightLiftingData.jsonData 103)

