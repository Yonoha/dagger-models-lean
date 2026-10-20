import OriginalCountableContinuousClassesRecovered
import OriginalSphereBoundaryRecovered
import Mathlib.Topology.CompactOpen
import OriginalRecoveredClosedExpressionApplication
import OriginalRecoveredCountableExtractionRealizationData

/-! Original CountableSphereQuotient, with unchanged closed types and values. -/

set_option autoImplicit false
set_option maxRecDepth 100000

noncomputable abbrev DaggerCountableSphereQuotient.Boundary.{u}
    (arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 12387
        [])
    :
    recovered_closed_result_type%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 12387
      [arg0]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 12387 :=
    @(recovered_closed_expr%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 12388)
  exact @f arg0

theorem DaggerCountableSphereQuotient.toSphere._proof_1.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 12540 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 12545)

noncomputable abbrev DaggerCountableSphereQuotient.toSphere.{u}
    (arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 11961
        [])
    :
    recovered_closed_result_type%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 11961
      [arg0]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 11961 :=
    @(recovered_closed_expr%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 11980)
  exact @f arg0

noncomputable def DaggerCountableSphereQuotient.backwardHomotopy.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 10917
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 10917
        [arg0]}
    {arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 10917
        [arg0, arg1]}
    {arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 10917
        [arg0, arg1, arg2]}
    (arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 10917
        [arg0, arg1, arg2, arg3])
    :
    recovered_closed_result_type%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 10917
      [arg0, arg1, arg2, arg3, arg4]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 10917 :=
    @(recovered_closed_expr%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 10933)
  exact @f arg0 arg1 arg2 arg3 arg4

noncomputable def DaggerCountableSphereQuotient.representative.{u}
    (arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 10941
        [])
    (arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 10941
        [arg0])
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 10941
        [arg0, arg1])
    :
    recovered_closed_result_type%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 10941
      [arg0, arg1, arg2]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 10941 :=
    @(recovered_closed_expr%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 10960)
  exact @f arg0 arg1 arg2

theorem DaggerCountableSphereQuotient.fromSphere._proof_1.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 12006 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 12012)

noncomputable abbrev DaggerCountableSphereQuotient.fromSphere.{u}
    (arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 12550
        [])
    :
    recovered_closed_result_type%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 12550
      [arg0]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 12550 :=
    @(recovered_closed_expr%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 12578)
  exact @f arg0

noncomputable def DaggerCountableSphereQuotient.forwardHomotopy.{u, u_1}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 11021
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 11021
        [arg0]}
    {arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 11021
        [arg0, arg1]}
    {arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 11021
        [arg0, arg1, arg2]}
    (arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 11021
        [arg0, arg1, arg2, arg3])
    :
    recovered_closed_result_type%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 11021
      [arg0, arg1, arg2, arg3, arg4]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 11021 :=
    @(recovered_closed_expr%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 11037)
  exact @f arg0 arg1 arg2 arg3 arg4

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerCountableSphereQuotient.representative.eq_1)
  pure ()

noncomputable abbrev DaggerCountableSphereQuotient.SphereClasses.{u}
    (arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 11343
        [])
    (arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 11343
        [arg0])
    :
    recovered_closed_result_type%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 11343
      [arg0, arg1]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 11343 :=
    @(recovered_closed_expr%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 11351)
  exact @f arg0 arg1

noncomputable def DaggerCountableSphereQuotient.continuousMapEquiv.{u}
    (arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 12036
        [])
    (arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 12036
        [arg0])
    :
    recovered_closed_result_type%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 12036
      [arg0, arg1]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 12036 :=
    @(recovered_closed_expr%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 12071)
  exact @f arg0 arg1

theorem DaggerCountableSphereQuotient.continuousMapEquiv_apply.{u} :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 11357 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 11403)

theorem DaggerCountableSphereQuotient.homotopic_continuousMapEquiv_iff.{u} :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 12113 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 12386)

noncomputable def DaggerCountableSphereQuotient.classesEquiv.{u}
    (arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 12014
        [])
    (arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 12014
        [arg0])
    :
    recovered_closed_result_type%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 12014
      [arg0, arg1]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 12014 :=
    @(recovered_closed_expr%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 12032)
  exact @f arg0 arg1

theorem DaggerCountableSphereQuotient.classesEquiv_mk.{u} :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 11124 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 11207)

theorem DaggerCountableSphereQuotient.continuousMapEquiv_symm_apply.{u} :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 11524 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 11569)

theorem DaggerCountableSphereQuotient.classesEquiv_symm_mk.{u} :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 11236 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 11314)

theorem DaggerCountableSphereQuotient.countable_sphere_classes.{u} :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 11321 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 11340)

noncomputable def DaggerCountableSphereQuotient.rawMap.{u}
    (arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 11467
        [])
    (arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 11467
        [arg0])
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredCountableExtractionRealizationData.jsonData 11467
        [arg0, arg1])
    :
    recovered_closed_result_type%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 11467
      [arg0, arg1, arg2]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 11467 :=
    @(recovered_closed_expr%
      DaggerRecoveredCountableExtractionRealizationData.jsonData 11470)
  exact @f arg0 arg1 arg2

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerCountableSphereQuotient.rawMap.eq_1)
  pure ()

theorem DaggerCountableSphereQuotient.rawMap_formula.{u} :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 11447 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 11464)

theorem DaggerCountableSphereQuotient.rawMap_surjective.{u} :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 11479 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 11518)

theorem DaggerCountableSphereQuotient.backwardHomotopy_apply.{u} :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 11693 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 11702)

theorem DaggerCountableSphereQuotient.rawMap_representative.{u} :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 11708 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 11952)

theorem DaggerCountableSphereQuotient.classesEquiv_right_inverse.{u} :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 12078 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 12086)

theorem DaggerCountableSphereQuotient.countable_raw_source.{u} :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 12418 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 12429)

theorem DaggerCountableSphereQuotient.countable_sphere_classes_via_raw.{u} :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 11321 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 12102)

theorem DaggerCountableSphereQuotient.classesEquiv_left_inverse.{u} :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 12395 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 12403)

theorem DaggerCountableSphereQuotient.boundary_finite.{u} :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 12406 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 12414)

theorem DaggerCountableSphereQuotient.forwardHomotopy_apply.{u} :
  recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 12513 :=
  @(recovered_closed_expr%
    DaggerRecoveredCountableExtractionRealizationData.jsonData 12521)

