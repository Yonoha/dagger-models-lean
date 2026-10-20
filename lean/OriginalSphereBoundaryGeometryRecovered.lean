import OriginalSphereBoundaryCoordinatesRecovered
import OriginalRecoveredClosedExpressionApplication
import OriginalRecoveredCountableExtractionRealizationData

/-! Original SphereBoundaryGeometry, with unchanged closed types and values. -/

set_option autoImplicit false
set_option maxRecDepth 100000

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerSphereBoundary.coordinateSimplex.eq_1)
  pure ()

theorem DaggerSphereBoundary.interior_coordinateSimplex :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 7547 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 8560)

theorem DaggerSphereBoundary.frontier_coordinateSimplex :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 8778 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 9292)

theorem DaggerSphereBoundary.drop_boundary_mem :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 9296 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 9848)

theorem DaggerSphereBoundary.boundaryCoordinatesHomeo._proof_1 :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 9860 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 9861)

theorem DaggerSphereBoundary.complete_frontier_mem :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 8588 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 8756)

theorem DaggerSphereBoundary.boundaryCoordinatesHomeo._proof_2 :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 6971 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 6978)

theorem DaggerSphereBoundary.boundaryCoordinatesHomeo._proof_3 :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 6990 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 7002)

theorem DaggerSphereBoundary.boundaryCoordinatesHomeo._proof_4 :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 9871 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 9891)

theorem DaggerSphereBoundary.boundaryCoordinatesHomeo._proof_5 :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 9851 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 9858)

theorem DaggerSphereBoundary.boundaryCoordinatesHomeo._proof_6 :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 6922 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 6968)

theorem DaggerSphereBoundary.boundaryCoordinatesHomeo._proof_7 :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 8759 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 8761)

theorem DaggerSphereBoundary.boundaryCoordinatesHomeo._proof_8 :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 7514 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 7540)

theorem DaggerSphereBoundary.boundaryCoordinatesHomeo._proof_9 :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 7542 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 7544)

theorem DaggerSphereBoundary.boundaryCoordinatesHomeo._proof_10 :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 7470 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 7495)

noncomputable def DaggerSphereBoundary.boundaryCoordinatesHomeo
    (arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 7426
        [])
    :
    recovered_closed_result_type%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 7426
      [arg0]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 7426 :=
    @(recovered_closed_expr%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 7450)
  exact @f arg0

theorem DaggerSphereBoundary.boundaryCoordinatesHomeo_symm_coe :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 6899 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 6902)

theorem DaggerSphereBoundary.interiorPoint._proof_1 :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 3930 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 3933)

noncomputable def DaggerSphereBoundary.interiorPoint
    (arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 8561
        [])
    :
    recovered_closed_result_type%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 8561
      [arg0]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 8561 :=
    @(recovered_closed_expr%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 8584)
  exact @f arg0

theorem DaggerSphereBoundary.interiorPoint_mem :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 7015 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 7417)

theorem DaggerSphereBoundary.boundaryCoordinatesHomeo_coe :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 9916 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 9919)

theorem DaggerSphereBoundary.interior_nonempty :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 9923 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 9934)

