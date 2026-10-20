import OriginalUnitaryDiscreteEnrichmentRecovered
import OriginalRecoveredClosedExpressionApplication
import OriginalRecoveredUnitaryDiscreteCoherentAlgebraData

/-! Original UnitaryDiscrete, with unchanged closed types and values. -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace DaggerUnitaryDiscrete
universe u
open CategoryTheory DaggerModels

noncomputable def unitaryValue (A : Type u) [Category.{u} A] [DaggerCategory A]
    (x y : A) (u0 : x ⟶ y) (a b : DaggerUnitaryInterval.Vertex.{u}) :
    (if a.down = true then y else x) ⟶ (if b.down = true then y else x) :=
  match a, b with
  | ⟨false⟩, ⟨false⟩ => 𝟙 x
  | ⟨false⟩, ⟨true⟩ => u0
  | ⟨true⟩, ⟨false⟩ => dagger u0
  | ⟨true⟩, ⟨true⟩ => 𝟙 y

end DaggerUnitaryDiscrete

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerUnitaryDiscrete.unitaryValue.match_1)
  pure ()

theorem DaggerUnitaryDiscrete.unitaryToCopy._proof_1.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 24218 :=
  @(recovered_closed_expr%
    DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 24226)

theorem DaggerUnitaryDiscrete.unitaryToCopy._proof_2.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 11039 :=
  @(recovered_closed_expr%
    DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 11053)

theorem DaggerUnitaryDiscrete.unitaryToCopy._proof_3.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 11112 :=
  @(recovered_closed_expr%
    DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 11384)

theorem DaggerUnitaryDiscrete.unitaryToCopy._proof_4.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 24260 :=
  @(recovered_closed_expr%
    DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 24267)

theorem DaggerUnitaryDiscrete.unitaryToCopy._proof_5.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 22851 :=
  @(recovered_closed_expr%
    DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 22859)

theorem DaggerUnitaryDiscrete.unitaryToCopy._proof_6.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 9688 :=
  @(recovered_closed_expr%
    DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 10695)

theorem DaggerUnitaryDiscrete.unitaryToCopy._proof_7.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 19838 :=
  @(recovered_closed_expr%
    DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 22159)

noncomputable def DaggerUnitaryDiscrete.unitaryToCopy.{u}
    (arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 13529
        [])
    [arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 13529
        [arg0]]
    [arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 13529
        [arg0, arg1]]
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 13529
        [arg0, arg1, arg2])
    (arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 13529
        [arg0, arg1, arg2, arg3])
    (arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 13529
        [arg0, arg1, arg2, arg3, arg4])
    (arg6 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 13529
        [arg0, arg1, arg2, arg3, arg4, arg5])
    :
    recovered_closed_result_type%
      DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 13529
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 13529 :=
    @(recovered_closed_expr%
      DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 13633)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5 arg6

noncomputable abbrev DaggerUnitaryDiscrete.fixedHomMap.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 26841
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 26841
        [arg0]}
    {arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 26841
        [arg0, arg1]}
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 26841
        [arg0, arg1, arg2])
    (arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 26841
        [arg0, arg1, arg2, arg3])
    (arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 26841
        [arg0, arg1, arg2, arg3, arg4])
    :
    recovered_closed_result_type%
      DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 26841
      [arg0, arg1, arg2, arg3, arg4, arg5]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 26841 :=
    @(recovered_closed_expr%
      DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 26855)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5

noncomputable def DaggerUnitaryDiscrete.walkingValue.{u}
    (arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 18470
        [])
    [arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 18470
        [arg0]]
    [arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 18470
        [arg0, arg1]]
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 18470
        [arg0, arg1, arg2])
    (arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 18470
        [arg0, arg1, arg2, arg3])
    (arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 18470
        [arg0, arg1, arg2, arg3, arg4])
    :
    recovered_closed_result_type%
      DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 18470
      [arg0, arg1, arg2, arg3, arg4, arg5]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 18470 :=
    @(recovered_closed_expr%
      DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 18480)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5

theorem DaggerUnitaryDiscrete.fixedHomMap_dagger.{u} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 25689 :=
  @(recovered_closed_expr%
    DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 26607)

theorem DaggerUnitaryDiscrete.fixedHomMap_comp.{u} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 24507 :=
  @(recovered_closed_expr%
    DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 25637)

theorem DaggerUnitaryDiscrete.fixedHomMap_id.{u} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 18590 :=
  @(recovered_closed_expr%
    DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 19600)

theorem DaggerUnitaryDiscrete.walkingValue_unitary.{u} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 12406 :=
  @(recovered_closed_expr%
    DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 13201)

theorem DaggerUnitaryDiscrete.fixedHom_ext.{u} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 13884 :=
  @(recovered_closed_expr%
    DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 18464)

theorem DaggerUnitaryDiscrete.unitaryToCopy_map.{u} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 24314 :=
  @(recovered_closed_expr%
    DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 24327)

theorem DaggerUnitaryDiscrete.point_map_all_degrees.{u} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 22754 :=
  @(recovered_closed_expr%
    DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 22843)

theorem DaggerUnitaryDiscrete.unitaryToCopy_walkingValue.{u} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 7751 :=
  @(recovered_closed_expr%
    DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 8733)

theorem DaggerRecoveredUnitaryDiscretePrivate.unitaryValueEq4.{u_1, u_2} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 8773 :=
  @(recovered_closed_expr%
    DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 8781)

noncomputable def DaggerUnitaryDiscrete.intervalValue.{u}
    (arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 8793
        [])
    [arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 8793
        [arg0]]
    [arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 8793
        [arg0, arg1]]
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 8793
        [arg0, arg1, arg2])
    (arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 8793
        [arg0, arg1, arg2, arg3])
    (arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 8793
        [arg0, arg1, arg2, arg3, arg4])
    (arg6 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 8793
        [arg0, arg1, arg2, arg3, arg4, arg5])
    :
    recovered_closed_result_type%
      DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 8793
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 8793 :=
    @(recovered_closed_expr%
      DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 8815)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5 arg6

theorem DaggerUnitaryDiscrete.walkingHomEquiv._proof_1.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 18487 :=
  @(recovered_closed_expr%
    DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 18493)

theorem DaggerUnitaryDiscrete.walkingHomEquiv._proof_2.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 9334 :=
  @(recovered_closed_expr%
    DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 9352)

theorem DaggerUnitaryDiscrete.walkingHomEquiv._proof_3.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 9375 :=
  @(recovered_closed_expr%
    DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 9449)

noncomputable def DaggerUnitaryDiscrete.walkingHomEquiv.{u}
    (arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 10712
        [])
    [arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 10712
        [arg0]]
    [arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 10712
        [arg0, arg1]]
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 10712
        [arg0, arg1, arg2])
    (arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 10712
        [arg0, arg1, arg2, arg3])
    :
    recovered_closed_result_type%
      DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 10712
      [arg0, arg1, arg2, arg3, arg4]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 10712 :=
    @(recovered_closed_expr%
      DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 10754)
  exact @f arg0 arg1 arg2 arg3 arg4

theorem DaggerUnitaryDiscrete.intervalValue_dagger.{u} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 22549 :=
  @(recovered_closed_expr%
    DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 22604)

theorem DaggerUnitaryDiscrete.intervalValue_unitary.{u} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 22867 :=
  @(recovered_closed_expr%
    DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 23993)

theorem DaggerUnitaryDiscrete.map_to_constant_of_subsingleton.{u} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 8885 :=
  @(recovered_closed_expr%
    DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 9020)

theorem DaggerUnitaryDiscrete.unitaryToCopy_intervalValue.{u} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 11418 :=
  @(recovered_closed_expr%
    DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 12399)

theorem DaggerUnitaryDiscrete.intervalHomEquiv._proof_1.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 22639 :=
  @(recovered_closed_expr%
    DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 22655)

theorem DaggerUnitaryDiscrete.intervalValue_precomp.{u} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 22171 :=
  @(recovered_closed_expr%
    DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 22255)

theorem DaggerUnitaryDiscrete.intervalHomEquiv._proof_2.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 26918 :=
  @(recovered_closed_expr%
    DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 26989)

noncomputable def DaggerUnitaryDiscrete.intervalHomEquiv.{u}
    (arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 13209
        [])
    [arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 13209
        [arg0]]
    [arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 13209
        [arg0, arg1]]
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 13209
        [arg0, arg1, arg2])
    (arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 13209
        [arg0, arg1, arg2, arg3])
    (arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 13209
        [arg0, arg1, arg2, arg3, arg4])
    :
    recovered_closed_result_type%
      DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 13209
      [arg0, arg1, arg2, arg3, arg4, arg5]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 13209 :=
    @(recovered_closed_expr%
      DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 13255)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5

noncomputable def DaggerUnitaryDiscrete.intervalFactorEquiv.{u}
    (arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 8823
        [])
    [arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 8823
        [arg0]]
    [arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 8823
        [arg0, arg1]]
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 8823
        [arg0, arg1, arg2])
    (arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 8823
        [arg0, arg1, arg2, arg3])
    (arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 8823
        [arg0, arg1, arg2, arg3, arg4])
    :
    recovered_closed_result_type%
      DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 8823
      [arg0, arg1, arg2, arg3, arg4, arg5]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 8823 :=
    @(recovered_closed_expr%
      DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 8862)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5

theorem DaggerUnitaryDiscrete.witnessAt_iff_unitary.{u} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 26645 :=
  @(recovered_closed_expr%
    DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 26813)

theorem DaggerUnitaryDiscrete.hasIntervalWitness_iff_unitary.{u} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 27003 :=
  @(recovered_closed_expr%
    DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 27069)

theorem DaggerUnitaryDiscrete.coherentlyUnitaryVertex_iff_unitary.{u} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 9037 :=
  @(recovered_closed_expr%
    DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 9283)

theorem DaggerUnitaryDiscrete.intervalFactorEquiv_apply.{u} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 22664 :=
  @(recovered_closed_expr%
    DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 22741)

theorem DaggerUnitaryDiscrete.interval_precomp_bijective.{u} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 9468 :=
  @(recovered_closed_expr%
    DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 9578)

theorem DaggerUnitaryDiscrete.intervalFactorEquiv_source_naturality.{u} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 10828 :=
  @(recovered_closed_expr%
    DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 10996)

theorem DaggerUnitaryDiscrete.interval_generator_fac.{u} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 13280 :=
  @(recovered_closed_expr%
    DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 13353)

theorem DaggerUnitaryDiscrete.standard_coherentlyUnitaryVertex_iff_unitary.{u} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 13367 :=
  @(recovered_closed_expr%
    DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 13381)

theorem DaggerUnitaryDiscrete.coherentlyUnitary_iff_unitary.{u} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 13416 :=
  @(recovered_closed_expr%
    DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 13522)

theorem DaggerUnitaryDiscrete.intervalFactorEquiv_symm_apply.{u} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 13661 :=
  @(recovered_closed_expr%
    DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 13670)

theorem DaggerUnitaryDiscrete.intervalValue_postcomp.{u} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 13713 :=
  @(recovered_closed_expr%
    DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 13815)

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerUnitaryDiscrete.unitaryValue.eq_3)
  pure ()

theorem DaggerUnitaryDiscrete.interval_factorization_unique.{u} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 22269 :=
  @(recovered_closed_expr%
    DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 22530)

theorem DaggerUnitaryDiscrete.intervalFactorEquiv_target_naturality.{u} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 24060 :=
  @(recovered_closed_expr%
    DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 24188)

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerUnitaryDiscrete.unitaryValue.eq_4)
  pure ()

theorem DaggerRecoveredUnitaryDiscretePrivate.unitaryValueEq3.{u_1, u_2} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 24282 :=
  @(recovered_closed_expr%
    DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 24289)

theorem DaggerUnitaryDiscrete.walkingValue_postcomp.{u} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 24360 :=
  @(recovered_closed_expr%
    DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 24440)

theorem DaggerRecoveredUnitaryDiscretePrivate.unitaryValueEq2.{u_1, u_2} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 26621 :=
  @(recovered_closed_expr%
    DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 26628)

noncomputable abbrev DaggerRecoveredUnitaryDiscretePrivate.unitaryValueSplitter.{u_1, u_2}
    (arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 19621
        [])
    (arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 19621
        [arg0])
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 19621
        [arg0, arg1])
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 19621
        [arg0, arg1, arg2])
    (arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 19621
        [arg0, arg1, arg2, arg3])
    (arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 19621
        [arg0, arg1, arg2, arg3, arg4])
    (arg6 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 19621
        [arg0, arg1, arg2, arg3, arg4, arg5])
    :
    recovered_closed_result_type%
      DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 19621
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 19621 :=
    @(recovered_closed_expr%
      DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 8757)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5 arg6

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerUnitaryDiscrete.unitaryValue.eq_2)
  pure ()

theorem DaggerRecoveredUnitaryDiscretePrivate.unitaryValueEq1.{u_1, u_2} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 26869 :=
  @(recovered_closed_expr%
    DaggerRecoveredUnitaryDiscreteCoherentAlgebraData.jsonData 26876)

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerUnitaryDiscrete.unitaryValue.eq_1)
  pure ()

