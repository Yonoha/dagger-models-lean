import OriginalSphereBoundaryRealizationRecovered
import Mathlib.Analysis.Convex.GaugeRescale
import OriginalRecoveredClosedExpressionApplication
import OriginalRecoveredCountableExtractionRealizationData

/-! Original SphereBoundaryCoordinates, with unchanged closed types and values. -/

set_option autoImplicit false
set_option maxRecDepth 100000

theorem DaggerSphereBoundary.dropLinear._proof_1 :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 2467 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 2473)

noncomputable abbrev DaggerSphereBoundary.E
    (arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 6712
        [])
    :
    recovered_closed_result_type%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 6712
      [arg0]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 6712 :=
    @(recovered_closed_expr%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 6716)
  exact @f arg0

noncomputable def DaggerSphereBoundary.coordinateSimplex
    (arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 4427
        [])
    :
    recovered_closed_result_type%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 4427
      [arg0]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 4427 :=
    @(recovered_closed_expr%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 4445)
  exact @f arg0

noncomputable def DaggerSphereBoundary.completeCoordinates
    (arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 3301
        [])
    (arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 3301
        [arg0])
    :
    recovered_closed_result_type%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 3301
      [arg0, arg1]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 3301 :=
    @(recovered_closed_expr%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 3303)
  exact @f arg0 arg1

theorem DaggerSphereBoundary.complete_mem :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 2492 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 3084)

noncomputable def DaggerSphereBoundary.sigma
    (arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 6779
        [])
    (arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 6779
        [arg0])
    :
    recovered_closed_result_type%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 6779
      [arg0, arg1]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 6779 :=
    @(recovered_closed_expr%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 6781)
  exact @f arg0 arg1

theorem DaggerSphereBoundary.sigmaLinear._proof_1 :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 4700 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 4785)

theorem DaggerSphereBoundary.sigmaLinear._proof_2 :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 3483 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 3644)

noncomputable def DaggerSphereBoundary.sigmaLinear
    (arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 3203
        [])
    :
    recovered_closed_result_type%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 3203
      [arg0]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 3203 :=
    @(recovered_closed_expr%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 3246)
  exact @f arg0

theorem DaggerSphereBoundary.dropCoordinates._proof_1 :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 3930 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 3933)

noncomputable def DaggerSphereBoundary.dropCoordinates
    (arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 3935
        [])
    (arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 3935
        [arg0])
    :
    recovered_closed_result_type%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 3935
      [arg0, arg1]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 3935 :=
    @(recovered_closed_expr%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 3942)
  exact @f arg0 arg1

theorem DaggerSphereBoundary.drop_mem :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 4980 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 5658)

theorem DaggerSphereBoundary.simplexCoordinatesHomeo._proof_7 :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 3259 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 3269)

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerSphereBoundary.completeCoordinates.eq_1)
  pure ()

theorem DaggerSphereBoundary.section._proof_1 :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 3739 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 3743)

noncomputable def DaggerSphereBoundary.section
    (arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 6820
        [])
    (arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 6820
        [arg0])
    :
    recovered_closed_result_type%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 6820
      [arg0, arg1]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 6820 :=
    @(recovered_closed_expr%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 6822)
  exact @f arg0 arg1

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerSphereBoundary.section.eq_1)
  pure ()

theorem DaggerSphereBoundary.sigma_section :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 6027 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 6159)

theorem DaggerSphereBoundary.sigma_surjective :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 3345 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 3360)

noncomputable def DaggerSphereBoundary.dropLinear
    (arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 5806
        [])
    :
    recovered_closed_result_type%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 5806
      [arg0]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 5806 :=
    @(recovered_closed_expr%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 5945)
  exact @f arg0

theorem DaggerSphereBoundary.dropLinear_apply :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 3727 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 3731)

theorem DaggerSphereBoundary.simplexCoordinatesHomeo._proof_9 :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 4882 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 4884)

theorem DaggerSphereBoundary.continuous_sigma :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 4939 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 4975)

theorem DaggerSphereBoundary.continuous_complete :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 4791 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 4850)

theorem DaggerSphereBoundary.simplexCoordinatesHomeo._proof_10 :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 3786 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 3833)

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerSphereBoundary.sigma.eq_1)
  pure ()

theorem DaggerSphereBoundary.simplexCoordinatesHomeo._proof_1 :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 3845 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 3847)

theorem DaggerSphereBoundary.simplexCoordinatesHomeo._proof_3 :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 6770 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 6777)

theorem DaggerSphereBoundary.complete_drop :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 6166 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 6710)

theorem DaggerSphereBoundary.simplexCoordinatesHomeo._proof_4 :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 3868 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 3926)

theorem DaggerSphereBoundary.drop_complete :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 4658 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 4672)

theorem DaggerSphereBoundary.image_dropLinear :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 3984 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 4426)

theorem DaggerSphereBoundary.sigma_open :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 4452 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 4653)

theorem DaggerSphereBoundary.simplexCoordinatesHomeo._proof_2 :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 6766 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 6767)

theorem DaggerSphereBoundary.simplexCoordinatesHomeo._proof_5 :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 6811 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 6818)

theorem DaggerSphereBoundary.simplexCoordinatesHomeo._proof_6 :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 4868 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 4879)

theorem DaggerSphereBoundary.continuous_drop :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 6722 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 6764)

theorem DaggerSphereBoundary.simplexCoordinatesHomeo._proof_8 :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 4902 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 4934)

noncomputable def DaggerSphereBoundary.simplexCoordinatesHomeo
    (arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 5664
        [])
    :
    recovered_closed_result_type%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 5664
      [arg0]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 5664 :=
    @(recovered_closed_expr%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 5690)
  exact @f arg0

theorem DaggerSphereBoundary.simplexCoordinatesHomeo_coe :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 5725 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 5728)

theorem DaggerSphereBoundary.simplexCoordinatesHomeo_symm_coe :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 5759 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 5762)

theorem DaggerSphereBoundary.compact_coordinateSimplex :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 5767 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 5805)

theorem DaggerSphereBoundary.convex_coordinateSimplex :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 5973 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 6022)

theorem DaggerSphereBoundary.closed_coordinateSimplex :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 6786 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 6808)

theorem DaggerSphereBoundary.bounded_coordinateSimplex :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 6836 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 6842)

