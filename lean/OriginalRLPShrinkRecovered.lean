import OriginalRLPSquaresRecovered
import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty
import OriginalRecoveredClosedExpressionApplication
import OriginalRecoveredRLPAccessibilityPipelineData

/-! Original RLPShrink, with unchanged closed types and values. -/

set_option autoImplicit false
set_option maxRecDepth 100000

theorem DaggerRLPAccessibility.rawLiftSource_small.{w, v, u, t} :
  recovered_closed_expr%
    DaggerRecoveredRLPAccessibilityPipelineData.jsonData 26983 :=
  @(recovered_closed_expr%
    DaggerRecoveredRLPAccessibilityPipelineData.jsonData 27014)
attribute [instance] DaggerRLPAccessibility.rawLiftSource_small

theorem DaggerRLPAccessibility.rawSourceFunctor_small.{w, v, u, t} :
  recovered_closed_expr%
    DaggerRecoveredRLPAccessibilityPipelineData.jsonData 22962 :=
  @(recovered_closed_expr%
    DaggerRecoveredRLPAccessibilityPipelineData.jsonData 22981)
attribute [instance] DaggerRLPAccessibility.rawSourceFunctor_small

theorem DaggerRLPAccessibility.rawTargetFunctor_small.{w, v, u, t} :
  recovered_closed_expr%
    DaggerRecoveredRLPAccessibilityPipelineData.jsonData 27526 :=
  @(recovered_closed_expr%
    DaggerRecoveredRLPAccessibilityPipelineData.jsonData 27562)
attribute [instance] DaggerRLPAccessibility.rawTargetFunctor_small

noncomputable def DaggerRLPAccessibility.liftNatural.{w, v, u, t}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredRLPAccessibilityPipelineData.jsonData 24539
        []}
    [arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredRLPAccessibilityPipelineData.jsonData 24539
        [arg0]]
    {arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredRLPAccessibilityPipelineData.jsonData 24539
        [arg0, arg1]}
    {arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredRLPAccessibilityPipelineData.jsonData 24539
        [arg0, arg1, arg2]}
    {arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredRLPAccessibilityPipelineData.jsonData 24539
        [arg0, arg1, arg2, arg3]}
    (arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredRLPAccessibilityPipelineData.jsonData 24539
        [arg0, arg1, arg2, arg3, arg4])
    [arg6 :
      recovered_closed_binder_type%
        DaggerRecoveredRLPAccessibilityPipelineData.jsonData 24539
        [arg0, arg1, arg2, arg3, arg4, arg5]]
    [arg7 :
      recovered_closed_binder_type%
        DaggerRecoveredRLPAccessibilityPipelineData.jsonData 24539
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6]]
    :
    recovered_closed_result_type%
      DaggerRecoveredRLPAccessibilityPipelineData.jsonData 24539
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredRLPAccessibilityPipelineData.jsonData 24539 :=
    @(recovered_closed_expr%
      DaggerRecoveredRLPAccessibilityPipelineData.jsonData 24562)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5 arg6 arg7

theorem DaggerRLPAccessibility.liftFunctor._proof_1.{u_1, u_2, u_3, u_4} :
  recovered_closed_expr%
    DaggerRecoveredRLPAccessibilityPipelineData.jsonData 23131 :=
  @(recovered_closed_expr%
    DaggerRecoveredRLPAccessibilityPipelineData.jsonData 23153)

theorem DaggerRLPAccessibility.liftFunctor._proof_4.{u_1, u_2, u_3, u_4} :
  recovered_closed_expr%
    DaggerRecoveredRLPAccessibilityPipelineData.jsonData 23293 :=
  @(recovered_closed_expr%
    DaggerRecoveredRLPAccessibilityPipelineData.jsonData 23316)

theorem DaggerRLPAccessibility.liftFunctor._proof_2.{u_1, u_2, u_3, u_4} :
  recovered_closed_expr%
    DaggerRecoveredRLPAccessibilityPipelineData.jsonData 26531 :=
  @(recovered_closed_expr%
    DaggerRecoveredRLPAccessibilityPipelineData.jsonData 26550)

theorem DaggerRLPAccessibility.liftFunctor._proof_3.{u_1, u_2, u_3, u_4} :
  recovered_closed_expr%
    DaggerRecoveredRLPAccessibilityPipelineData.jsonData 26665 :=
  @(recovered_closed_expr%
    DaggerRecoveredRLPAccessibilityPipelineData.jsonData 26957)

theorem DaggerRLPAccessibility.liftFunctor._proof_5.{u_1, u_2, u_3, u_4} :
  recovered_closed_expr%
    DaggerRecoveredRLPAccessibilityPipelineData.jsonData 25928 :=
  @(recovered_closed_expr%
    DaggerRecoveredRLPAccessibilityPipelineData.jsonData 26408)

noncomputable def DaggerRLPAccessibility.liftFunctor.{w, v, u, t}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredRLPAccessibilityPipelineData.jsonData 26416
        []}
    [arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredRLPAccessibilityPipelineData.jsonData 26416
        [arg0]]
    {arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredRLPAccessibilityPipelineData.jsonData 26416
        [arg0, arg1]}
    {arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredRLPAccessibilityPipelineData.jsonData 26416
        [arg0, arg1, arg2]}
    {arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredRLPAccessibilityPipelineData.jsonData 26416
        [arg0, arg1, arg2, arg3]}
    (arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredRLPAccessibilityPipelineData.jsonData 26416
        [arg0, arg1, arg2, arg3, arg4])
    [arg6 :
      recovered_closed_binder_type%
        DaggerRecoveredRLPAccessibilityPipelineData.jsonData 26416
        [arg0, arg1, arg2, arg3, arg4, arg5]]
    [arg7 :
      recovered_closed_binder_type%
        DaggerRecoveredRLPAccessibilityPipelineData.jsonData 26416
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6]]
    :
    recovered_closed_result_type%
      DaggerRecoveredRLPAccessibilityPipelineData.jsonData 26416
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredRLPAccessibilityPipelineData.jsonData 26416 :=
    @(recovered_closed_expr%
      DaggerRecoveredRLPAccessibilityPipelineData.jsonData 26424)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5 arg6 arg7

theorem DaggerRLPAccessibility.rawLiftMap_surjective_iff_rlp.{v, u, t} :
  recovered_closed_expr%
    DaggerRecoveredRLPAccessibilityPipelineData.jsonData 25104 :=
  @(recovered_closed_expr%
    DaggerRecoveredRLPAccessibilityPipelineData.jsonData 25515)

theorem DaggerRLPAccessibility.squareTargetEquiv._proof_1.{u_1, u_2, u_3, u_4} :
  recovered_closed_expr%
    DaggerRecoveredRLPAccessibilityPipelineData.jsonData 27703 :=
  @(recovered_closed_expr%
    DaggerRecoveredRLPAccessibilityPipelineData.jsonData 27724)

noncomputable def DaggerRLPAccessibility.squareTargetEquiv.{w, v, u, t}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredRLPAccessibilityPipelineData.jsonData 27038
        []}
    [arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredRLPAccessibilityPipelineData.jsonData 27038
        [arg0]]
    {arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredRLPAccessibilityPipelineData.jsonData 27038
        [arg0, arg1]}
    {arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredRLPAccessibilityPipelineData.jsonData 27038
        [arg0, arg1, arg2]}
    {arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredRLPAccessibilityPipelineData.jsonData 27038
        [arg0, arg1, arg2, arg3]}
    (arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredRLPAccessibilityPipelineData.jsonData 27038
        [arg0, arg1, arg2, arg3, arg4])
    [arg6 :
      recovered_closed_binder_type%
        DaggerRecoveredRLPAccessibilityPipelineData.jsonData 27038
        [arg0, arg1, arg2, arg3, arg4, arg5]]
    [arg7 :
      recovered_closed_binder_type%
        DaggerRecoveredRLPAccessibilityPipelineData.jsonData 27038
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6]]
    (arg8 :
      recovered_closed_binder_type%
        DaggerRecoveredRLPAccessibilityPipelineData.jsonData 27038
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7])
    :
    recovered_closed_result_type%
      DaggerRecoveredRLPAccessibilityPipelineData.jsonData 27038
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredRLPAccessibilityPipelineData.jsonData 27038 :=
    @(recovered_closed_expr%
      DaggerRecoveredRLPAccessibilityPipelineData.jsonData 27058)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5 arg6 arg7 arg8

noncomputable def DaggerRLPAccessibility.liftSourceEquiv.{w, v, u, t}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredRLPAccessibilityPipelineData.jsonData 27289
        []}
    [arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredRLPAccessibilityPipelineData.jsonData 27289
        [arg0]]
    {arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredRLPAccessibilityPipelineData.jsonData 27289
        [arg0, arg1]}
    {arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredRLPAccessibilityPipelineData.jsonData 27289
        [arg0, arg1, arg2]}
    {arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredRLPAccessibilityPipelineData.jsonData 27289
        [arg0, arg1, arg2, arg3]}
    (arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredRLPAccessibilityPipelineData.jsonData 27289
        [arg0, arg1, arg2, arg3, arg4])
    [arg6 :
      recovered_closed_binder_type%
        DaggerRecoveredRLPAccessibilityPipelineData.jsonData 27289
        [arg0, arg1, arg2, arg3, arg4, arg5]]
    [arg7 :
      recovered_closed_binder_type%
        DaggerRecoveredRLPAccessibilityPipelineData.jsonData 27289
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6]]
    (arg8 :
      recovered_closed_binder_type%
        DaggerRecoveredRLPAccessibilityPipelineData.jsonData 27289
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7])
    :
    recovered_closed_result_type%
      DaggerRecoveredRLPAccessibilityPipelineData.jsonData 27289
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredRLPAccessibilityPipelineData.jsonData 27289 :=
    @(recovered_closed_expr%
      DaggerRecoveredRLPAccessibilityPipelineData.jsonData 27298)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5 arg6 arg7 arg8

theorem DaggerRLPAccessibility.liftFunctor_hom_decode.{w, v, u, t} :
  recovered_closed_expr%
    DaggerRecoveredRLPAccessibilityPipelineData.jsonData 24703 :=
  @(recovered_closed_expr%
    DaggerRecoveredRLPAccessibilityPipelineData.jsonData 24853)

theorem DaggerRLPAccessibility.liftFunctor_hom_encode.{w, v, u, t} :
  recovered_closed_expr%
    DaggerRecoveredRLPAccessibilityPipelineData.jsonData 25555 :=
  @(recovered_closed_expr%
    DaggerRecoveredRLPAccessibilityPipelineData.jsonData 25702)

theorem DaggerRLPAccessibility.liftFunctor_surjective_iff_rlp.{w, v, u, t} :
  recovered_closed_expr%
    DaggerRecoveredRLPAccessibilityPipelineData.jsonData 23418 :=
  @(recovered_closed_expr%
    DaggerRecoveredRLPAccessibilityPipelineData.jsonData 24210)

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerRLPAccessibility.rawLiftSourceFunctor.eq_1)
  pure ()

theorem DaggerRLPAccessibility.liftFunctor_map_left_encode.{w, v, u, t} :
  recovered_closed_expr%
    DaggerRecoveredRLPAccessibilityPipelineData.jsonData 24351 :=
  @(recovered_closed_expr%
    DaggerRecoveredRLPAccessibilityPipelineData.jsonData 24472)

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerRLPAccessibility.liftSourceEquiv.eq_1)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerRLPAccessibility.liftFunctor.eq_1)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerRLPAccessibility.rawSquareTargetFunctor.eq_1)
  pure ()

theorem DaggerRLPAccessibility.liftFunctor_map_right_encode.{w, v, u, t} :
  recovered_closed_expr%
    DaggerRecoveredRLPAccessibilityPipelineData.jsonData 27141 :=
  @(recovered_closed_expr%
    DaggerRecoveredRLPAccessibilityPipelineData.jsonData 27249)

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerRLPAccessibility.liftNatural.eq_1)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `CategoryTheory.FunctorToTypes.shrinkMap.eq_1)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerRLPAccessibility.squareTargetEquiv.eq_1)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerRLPAccessibility.rawLiftNatural.eq_1)
  pure ()

