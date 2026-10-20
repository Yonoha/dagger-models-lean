import OriginalCountableExtractionStepsRecovered
import OriginalRecoveredClosedExpressionApplication
import OriginalRecoveredCountableExtractionRealizationData

/-! Original CountableExtractionInner, with unchanged closed types and values. -/

set_option autoImplicit false
set_option maxRecDepth 100000

theorem DaggerCountableExtraction.initialState._proof_1.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 36312 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 36318)

noncomputable def DaggerCountableExtraction.initialState.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 38215
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 38215
        [arg0]}
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 38215
        [arg0, arg1])
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 38215
        [arg0, arg1, arg2])
    :
    recovered_closed_result_type%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 38215
      [arg0, arg1, arg2, arg3]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 38215 :=
    @(recovered_closed_expr%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 38232)
  exact @f arg0 arg1 arg2 arg3

namespace DaggerCountableExtraction
universe u
open CategoryTheory DaggerModels

noncomputable def innerState
    {K0 G : FixedDaggerSimplicialCat.{u} DaggerUnitaryInterval.Vertex}
    (phi0 : K0 ⟶ G) (hK0 : DaggerUnitaryInterval.CountableHoms K0)
    (hG0 : HomNonempty G) (hGW : GeometricContractible G) : ℕ → KillingState phi0
  | 0 => initialState phi0 hK0
  | n + 1 => (killingStep hK0 hG0 hGW (innerState phi0 hK0 hG0 hGW n) n).next

end DaggerCountableExtraction

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload (Lean.mkIdent `DaggerCountableExtraction.innerState._sunfold)
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload (Lean.mkIdent `DaggerCountableExtraction.innerState.match_1)
  pure ()

noncomputable def DaggerCountableExtraction.innerArrow.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 36895
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 36895
        [arg0]}
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 36895
        [arg0, arg1])
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 36895
        [arg0, arg1, arg2])
    (arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 36895
        [arg0, arg1, arg2, arg3])
    (arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 36895
        [arg0, arg1, arg2, arg3, arg4])
    (arg6 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 36895
        [arg0, arg1, arg2, arg3, arg4, arg5])
    :
    recovered_closed_result_type%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 36895
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 36895 :=
    @(recovered_closed_expr%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 36904)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5 arg6

noncomputable def DaggerCountableExtraction.innerF.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 38571
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 38571
        [arg0]}
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 38571
        [arg0, arg1])
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 38571
        [arg0, arg1, arg2])
    (arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 38571
        [arg0, arg1, arg2, arg3])
    (arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 38571
        [arg0, arg1, arg2, arg3, arg4])
    :
    recovered_closed_result_type%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 38571
      [arg0, arg1, arg2, arg3, arg4, arg5]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 38571 :=
    @(recovered_closed_expr%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 38577)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5

theorem DaggerCountableExtraction.innerCocone._proof_1.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 38276 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 38291)

noncomputable def DaggerCountableExtraction.innerCocone.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 37830
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 37830
        [arg0]}
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 37830
        [arg0, arg1])
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 37830
        [arg0, arg1, arg2])
    (arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 37830
        [arg0, arg1, arg2, arg3])
    (arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 37830
        [arg0, arg1, arg2, arg3, arg4])
    :
    recovered_closed_result_type%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 37830
      [arg0, arg1, arg2, arg3, arg4, arg5]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 37830 :=
    @(recovered_closed_expr%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 37843)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5

noncomputable abbrev DaggerCountableExtraction.innerTarget.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 36610
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 36610
        [arg0]}
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 36610
        [arg0, arg1])
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 36610
        [arg0, arg1, arg2])
    (arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 36610
        [arg0, arg1, arg2, arg3])
    (arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 36610
        [arg0, arg1, arg2, arg3, arg4])
    :
    recovered_closed_result_type%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 36610
      [arg0, arg1, arg2, arg3, arg4, arg5]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 36610 :=
    @(recovered_closed_expr%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 36624)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5

noncomputable def DaggerCountableExtraction.innerLeg.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 36272
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 36272
        [arg0]}
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 36272
        [arg0, arg1])
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 36272
        [arg0, arg1, arg2])
    (arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 36272
        [arg0, arg1, arg2, arg3])
    (arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 36272
        [arg0, arg1, arg2, arg3, arg4])
    (arg6 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 36272
        [arg0, arg1, arg2, arg3, arg4, arg5])
    :
    recovered_closed_result_type%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 36272
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 36272 :=
    @(recovered_closed_expr%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 36298)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5 arg6

noncomputable def DaggerCountableExtraction.innerIsColimit.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 37045
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 37045
        [arg0]}
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 37045
        [arg0, arg1])
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 37045
        [arg0, arg1, arg2])
    (arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 37045
        [arg0, arg1, arg2, arg3])
    (arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 37045
        [arg0, arg1, arg2, arg3, arg4])
    :
    recovered_closed_result_type%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 37045
      [arg0, arg1, arg2, arg3, arg4, arg5]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 37045 :=
    @(recovered_closed_expr%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 37065)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5

theorem DaggerCountableExtraction.innerToG._proof_1 :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 36262 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 36263)

theorem DaggerCountableExtraction.innerToG._proof_2.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 36935 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 37005)

noncomputable def DaggerCountableExtraction.innerToG.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 36012
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 36012
        [arg0]}
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 36012
        [arg0, arg1])
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 36012
        [arg0, arg1, arg2])
    (arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 36012
        [arg0, arg1, arg2, arg3])
    (arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 36012
        [arg0, arg1, arg2, arg3, arg4])
    :
    recovered_closed_result_type%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 36012
      [arg0, arg1, arg2, arg3, arg4, arg5]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 36012 :=
    @(recovered_closed_expr%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 36031)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5

noncomputable def DaggerCountableExtraction.innerPsi.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 37581
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 37581
        [arg0]}
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 37581
        [arg0, arg1])
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 37581
        [arg0, arg1, arg2])
    (arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 37581
        [arg0, arg1, arg2, arg3])
    (arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 37581
        [arg0, arg1, arg2, arg3, arg4])
    :
    recovered_closed_result_type%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 37581
      [arg0, arg1, arg2, arg3, arg4, arg5]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 37581 :=
    @(recovered_closed_expr%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 37610)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5

theorem DaggerCountableExtraction.innerLeg_psi.{u} :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 37854 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 37875)

theorem DaggerCountableExtraction.innerLeg_psi_assoc.{u} :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 35768 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 35910)

theorem DaggerCountableExtraction.innerBaseNat._proof_1.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 36116 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 36257)

noncomputable def DaggerCountableExtraction.innerBaseNat.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 35930
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 35930
        [arg0]}
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 35930
        [arg0, arg1])
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 35930
        [arg0, arg1, arg2])
    (arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 35930
        [arg0, arg1, arg2, arg3])
    (arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 35930
        [arg0, arg1, arg2, arg3, arg4])
    :
    recovered_closed_result_type%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 35930
      [arg0, arg1, arg2, arg3, arg4, arg5]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 35930 :=
    @(recovered_closed_expr%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 35960)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5

theorem DaggerCountableExtraction.inner_step_cof.{u} :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 35982 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 36003)

noncomputable def DaggerCountableExtraction.innerDesc.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 38047
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 38047
        [arg0]}
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 38047
        [arg0, arg1])
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 38047
        [arg0, arg1, arg2])
    (arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 38047
        [arg0, arg1, arg2, arg3])
    (arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 38047
        [arg0, arg1, arg2, arg3, arg4])
    (arg6 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 38047
        [arg0, arg1, arg2, arg3, arg4, arg5])
    :
    recovered_closed_result_type%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 38047
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 38047 :=
    @(recovered_closed_expr%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 38058)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5 arg6

theorem DaggerCountableExtraction.innerDesc_fac.{u} :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 36415 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 36446)

noncomputable def DaggerCountableExtraction.innerInclusion.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 37560
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 37560
        [arg0]}
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 37560
        [arg0, arg1])
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 37560
        [arg0, arg1, arg2])
    (arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 37560
        [arg0, arg1, arg2, arg3])
    (arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 37560
        [arg0, arg1, arg2, arg3, arg4])
    :
    recovered_closed_result_type%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 37560
      [arg0, arg1, arg2, arg3, arg4, arg5]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 37560 :=
    @(recovered_closed_expr%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 37573)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5

theorem DaggerCountableExtraction.inner_arrow_leg.{u} :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 36634 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 36842)

theorem DaggerCountableExtraction.inner_base_from_zero.{u} :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 37885 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 38037)

theorem DaggerCountableExtraction.inner_base_leg.{u} :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 37617 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 37697)

theorem DaggerCountableExtraction.inner_base_arrow_leg.{u} :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 36544 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 36604)

noncomputable def DaggerCountableExtraction.innerComposition.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 36870
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 36870
        [arg0]}
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 36870
        [arg0, arg1])
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 36870
        [arg0, arg1, arg2])
    (arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 36870
        [arg0, arg1, arg2, arg3])
    (arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 36870
        [arg0, arg1, arg2, arg3, arg4])
    :
    recovered_closed_result_type%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 36870
      [arg0, arg1, arg2, arg3, arg4, arg5]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 36870 :=
    @(recovered_closed_expr%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 36887)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5

theorem DaggerCountableExtraction.inner_countable.{u} :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 37012 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 37035)

theorem DaggerCountableExtraction.innerInclusion_psi.{u} :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 38198 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 38211)

theorem DaggerCountableExtraction.innerInclusion_psi_assoc.{u} :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 37096 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 37174)

theorem DaggerCountableExtraction.inner_arrow_leg_assoc.{u} :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 37210 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 37289)

theorem DaggerCountableExtraction.inner_step_mono.{u} :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 37805 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 37824)

theorem DaggerCountableExtraction.inner_mono.{u} :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 37358 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 37553)

theorem DaggerCountableExtraction.inner_over.{u} :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 37713 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 37725)

theorem DaggerCountableExtraction.innerDesc_uniq.{u} :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 38100 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 38190)

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerCountableExtraction.innerF.eq_1)
  pure ()

theorem DaggerCountableExtraction.inner_naturality.{u} :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 38323 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 38355)

theorem DaggerCountableExtraction.inner_cof.{u} :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 38365 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 38429)

theorem DaggerCountableExtraction.inner_kills_class.{u} :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 38682 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 39550)

theorem DaggerCountableExtraction.inner_kills.{u} :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 38485 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 38565)

