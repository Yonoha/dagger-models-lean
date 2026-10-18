import OriginalDKHomRetractsRecovered
import OriginalRecoveredClosedExpressionApplication
import OriginalRecoveredGlobalModelConstructionData

/-! Original DKCompositionReflection, with unchanged closed types and values. -/

set_option autoImplicit false
set_option maxRecDepth 100000

theorem DaggerGlobalDKClosure.daggerDK_of_postcomp.{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalModelConstructionData.jsonData 50 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalModelConstructionData.jsonData 789)

theorem DaggerGlobalDKClosure.daggerDK_comp.{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalModelConstructionData.jsonData 810 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalModelConstructionData.jsonData 1223)

theorem DaggerGlobalDKClosure.daggerDK_retractStable.{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalModelConstructionData.jsonData 1229 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalModelConstructionData.jsonData 1267)

