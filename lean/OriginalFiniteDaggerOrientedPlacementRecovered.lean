import OriginalFiniteDaggerCellSwapRecovered
import FixedCategoryPlacementComparison
import FixedCategoryHomLimits
import OriginalRecoveredClosedExpressionApplication
import OriginalRecoveredFinitePrivateExpression
import OriginalRecoveredFiniteRelativeCellFoundationData

/-! Original FiniteDaggerOrientedPlacement, with unchanged closed types and values. -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace DaggerFiniteDaggerExtension
universe u
open CategoryTheory DaggerModels

noncomputable def orientedBeta {O : Type u} (s : DaggerFixedGraphGenerators.Position O) :
    (reverse : Bool) → (T : SSet.{u}) →
      TwoObjectDaggerCell.cell T ⟶ (DaggerFixedCategoryPlacementComparison.freePlaced s T).toCat
  | false, T => DaggerFixedCategoryPlacementComparison.beta s T
  | true, T => (cellSwap T).hom ≫ DaggerFixedCategoryPlacementComparison.beta s T

end DaggerFiniteDaggerExtension

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `CategoryTheory.EnrichedFunctor.mk.congr_simp)
  pure ()

noncomputable abbrev DaggerFiniteDaggerExtension.orderedSource.match_1.{u_1}
    (arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 19498
        [])
    (arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 19498
        [arg0])
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 19498
        [arg0, arg1])
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 19498
        [arg0, arg1, arg2])
    :
    recovered_closed_result_type%
      DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 19498
      [arg0, arg1, arg2, arg3]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 19498 :=
    @(recovered_finite_private_expr%
      DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 19510)
  exact @f arg0 arg1 arg2 arg3

noncomputable def DaggerFiniteDaggerExtension.orderedSource.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 24912
        []}
    (arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 24912
        [arg0])
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 24912
        [arg0, arg1])
    :
    recovered_closed_result_type%
      DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 24912
      [arg0, arg1, arg2]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 24912 :=
    @(recovered_finite_private_expr%
      DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 25810)
  exact @f arg0 arg1 arg2

noncomputable def DaggerFiniteDaggerExtension.orderedTarget.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 24912
        []}
    (arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 24912
        [arg0])
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 24912
        [arg0, arg1])
    :
    recovered_closed_result_type%
      DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 24912
      [arg0, arg1, arg2]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 24912 :=
    @(recovered_finite_private_expr%
      DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 24923)
  exact @f arg0 arg1 arg2

structure DaggerFiniteDaggerExtension.OrderedPosition.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 25805
        []}
    (arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 25805
        [arg0])
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 25805
        [arg0, arg1])
    :
      recovered_closed_result_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 25805
        [arg0, arg1, arg2] where
  position :
    recovered_closed_binder_type%
      DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 6132
      [arg0, arg1, arg2]
  reverse :
    recovered_closed_binder_type%
      DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 6132
      [arg0, arg1, arg2, position]
  source_eq :
    recovered_closed_binder_type%
      DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 6132
      [arg0, arg1, arg2, position, reverse]
  target_eq :
    recovered_closed_binder_type%
      DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 6132
      [arg0, arg1, arg2, position, reverse, source_eq]

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteDaggerExtension.OrderedPosition)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteDaggerExtension.OrderedPosition._sizeOf_1)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteDaggerExtension.OrderedPosition._sizeOf_inst)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteDaggerExtension.OrderedPosition.casesOn)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteDaggerExtension.OrderedPosition.ctorIdx)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteDaggerExtension.OrderedPosition.mk)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteDaggerExtension.OrderedPosition.mk._flat_ctor)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteDaggerExtension.OrderedPosition.mk.inj)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteDaggerExtension.OrderedPosition.mk.injEq)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteDaggerExtension.OrderedPosition.mk.noConfusion)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteDaggerExtension.OrderedPosition.mk.sizeOf_spec)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteDaggerExtension.OrderedPosition.noConfusion)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteDaggerExtension.OrderedPosition.noConfusionType)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteDaggerExtension.OrderedPosition.position)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteDaggerExtension.OrderedPosition.rec)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteDaggerExtension.OrderedPosition.recOn)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteDaggerExtension.OrderedPosition.reverse)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteDaggerExtension.OrderedPosition.source_eq)
  pure ()

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteDaggerExtension.OrderedPosition.target_eq)
  pure ()

noncomputable def DaggerFiniteDaggerExtension.scalarEquiv.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 4474
        []}
    (arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 4474
        [arg0])
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 4474
        [arg0, arg1])
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 4474
        [arg0, arg1, arg2])
    :
    recovered_closed_result_type%
      DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 4474
      [arg0, arg1, arg2, arg3]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 4474 :=
    @(recovered_finite_private_expr%
      DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 4538)
  exact @f arg0 arg1 arg2 arg3

theorem DaggerFiniteDaggerExtension.scalarClassify_left._simp_1_3.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 4553 :=
  @(recovered_finite_private_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 4564)

theorem DaggerFiniteDaggerExtension.cellSwap_generator.{u} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 29258 :=
  @(recovered_finite_private_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 29306)

theorem DaggerFiniteDaggerExtension.reverse_generator.{u} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 5513 :=
  @(recovered_finite_private_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 5569)

theorem DaggerFiniteDaggerExtension.cellSwap_homEquiv.{u} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 4763 :=
  @(recovered_finite_private_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 5484)

theorem DaggerFiniteDaggerExtension.strict_scalar_boundary._simp_1_3.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 4553 :=
  @(recovered_finite_private_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 4564)

theorem DaggerFiniteDaggerExtension.orientedClassify_right._simp_1_3.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 4553 :=
  @(recovered_finite_private_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 4564)

theorem DaggerFiniteDaggerExtension.orientedClassify_left._simp_1_2.{u_1, u_4} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 5606 :=
  @(recovered_finite_private_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 5622)

noncomputable abbrev DaggerRecoveredFinitePrivate.orientedBetaSplitter.{u_1, u_2}
    (arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 5636
        [])
    (arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 5636
        [arg0])
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 5636
        [arg0, arg1])
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 5636
        [arg0, arg1, arg2])
    (arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 5636
        [arg0, arg1, arg2, arg3])
    :
    recovered_closed_result_type%
      DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 5636
      [arg0, arg1, arg2, arg3, arg4]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 5636 :=
    @(recovered_finite_private_expr%
      DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 5637)
  exact @f arg0 arg1 arg2 arg3 arg4

theorem DaggerFiniteDaggerExtension.orderedPosition._proof_4.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 5841 :=
  @(recovered_finite_private_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 5848)

theorem DaggerRecoveredFinitePrivate.orientedBetaEq2.{u_1, u_2} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 5869 :=
  @(recovered_finite_private_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 5876)

theorem DaggerFiniteDaggerExtension.orderedPosition._proof_1.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 5893 :=
  @(recovered_finite_private_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 5898)

theorem DaggerFiniteDaggerExtension.orderedPosition._proof_5.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 5991 :=
  @(recovered_finite_private_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 6012)

noncomputable def DaggerFiniteDaggerExtension.scalarClassify.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 29604
        []}
    (arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 29604
        [arg0])
    {arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 29604
        [arg0, arg1]}
    {arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 29604
        [arg0, arg1, arg2]}
    (arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 29604
        [arg0, arg1, arg2, arg3])
    :
    recovered_closed_result_type%
      DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 29604
      [arg0, arg1, arg2, arg3, arg4]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 29604 :=
    @(recovered_finite_private_expr%
      DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 29609)
  exact @f arg0 arg1 arg2 arg3 arg4

theorem DaggerFiniteDaggerExtension.reverseScalarEquiv._proof_1.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 30708 :=
  @(recovered_finite_private_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 30834)

theorem DaggerFiniteDaggerExtension.reverseScalarEquiv._proof_2.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 26000 :=
  @(recovered_finite_private_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 26204)

noncomputable def DaggerFiniteDaggerExtension.reverseScalarEquiv.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 26212
        []}
    (arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 26212
        [arg0])
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 26212
        [arg0, arg1])
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 26212
        [arg0, arg1, arg2])
    :
    recovered_closed_result_type%
      DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 26212
      [arg0, arg1, arg2, arg3]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 26212 :=
    @(recovered_finite_private_expr%
      DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 26253)
  exact @f arg0 arg1 arg2 arg3

noncomputable def DaggerFiniteDaggerExtension.orientedEquiv.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 26260
        []}
    (arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 26260
        [arg0])
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 26260
        [arg0, arg1])
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 26260
        [arg0, arg1, arg2])
    (arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 26260
        [arg0, arg1, arg2, arg3])
    :
    recovered_closed_result_type%
      DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 26260
      [arg0, arg1, arg2, arg3, arg4]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 26260 :=
    @(recovered_finite_private_expr%
      DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 26311)
  exact @f arg0 arg1 arg2 arg3 arg4

noncomputable def DaggerFiniteDaggerExtension.orientedClassify.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 19527
        []}
    (arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 19527
        [arg0])
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 19527
        [arg0, arg1])
    {arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 19527
        [arg0, arg1, arg2]}
    {arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 19527
        [arg0, arg1, arg2, arg3]}
    (arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 19527
        [arg0, arg1, arg2, arg3, arg4])
    :
    recovered_closed_result_type%
      DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 19527
      [arg0, arg1, arg2, arg3, arg4, arg5]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 19527 :=
    @(recovered_finite_private_expr%
      DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 19533)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteDaggerExtension.orientedClassify.eq_1)
  pure ()

theorem DaggerFiniteDaggerExtension.orderedPosition._proof_7.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 6238 :=
  @(recovered_finite_private_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 6242)

noncomputable def DaggerFiniteDaggerExtension.orientedCellPushout.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 6457
        []}
    (arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 6457
        [arg0])
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 6457
        [arg0, arg1])
    {arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 6457
        [arg0, arg1, arg2]}
    {arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 6457
        [arg0, arg1, arg2, arg3]}
    (arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 6457
        [arg0, arg1, arg2, arg3, arg4])
    {arg6 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 6457
        [arg0, arg1, arg2, arg3, arg4, arg5]}
    {arg7 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 6457
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6]}
    (arg8 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 6457
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7])
    (arg9 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 6457
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8])
    (arg10 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 6457
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9])
    (arg11 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 6457
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10])
    :
    recovered_closed_result_type%
      DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 6457
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 6457 :=
    @(recovered_finite_private_expr%
      DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 7004)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5 arg6 arg7 arg8 arg9 arg10 arg11

theorem DaggerFiniteDaggerExtension.orderedPosition._proof_2.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 7012 :=
  @(recovered_finite_private_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 7017)

theorem DaggerFiniteDaggerExtension.orderedPosition._proof_3.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 7025 :=
  @(recovered_finite_private_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 7030)

theorem DaggerFiniteDaggerExtension.scalarEquiv_apply.{u} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 7192 :=
  @(recovered_finite_private_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 12680)

theorem DaggerFiniteDaggerExtension.strict_scalar_boundary._simp_1_2.{u_1, u_4} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 5606 :=
  @(recovered_finite_private_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 5622)

theorem DaggerFiniteDaggerExtension.orientedEquiv_apply.{u} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 25164 :=
  @(recovered_finite_private_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 25802)

theorem DaggerFiniteDaggerExtension.strict_scalar_boundary.{u} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 12789 :=
  @(recovered_finite_private_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 19256)

theorem DaggerFiniteDaggerExtension.scalarClassify_whole.{u} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 19322 :=
  @(recovered_finite_private_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 19491)

theorem DaggerFiniteDaggerExtension.scalarClassify_left._simp_1_2.{u_1, u_4} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 5606 :=
  @(recovered_finite_private_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 5622)

theorem DaggerFiniteDaggerExtension.orientedClassify_right._simp_1_2.{u_1, u_4} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 5606 :=
  @(recovered_finite_private_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 5622)

theorem DaggerFiniteDaggerExtension.orientedClassify_right.{u} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 19585 :=
  @(recovered_finite_private_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 24400)

theorem DaggerFiniteDaggerExtension.orientedBeta_naturality.{u} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 24511 :=
  @(recovered_finite_private_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 24909)

theorem DaggerRecoveredFinitePrivate.orientedBetaEq1.{u_1, u_2} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 25832 :=
  @(recovered_finite_private_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 25838)

theorem DaggerFiniteDaggerExtension.orientedClassify_left._simp_1_3.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 4553 :=
  @(recovered_finite_private_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 4564)

theorem DaggerFiniteDaggerExtension.orderedPosition._proof_6.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 26448 :=
  @(recovered_finite_private_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 26451)

theorem DaggerFiniteDaggerExtension.orientedClassify_whole.{u} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 26507 :=
  @(recovered_finite_private_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 26680)

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerModels.DaggerSimplicialCat.Hom.mk.congr_simp)
  pure ()

theorem DaggerFiniteDaggerExtension.orientedClassify_left.{u} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 28051 :=
  @(recovered_finite_private_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 29239)

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteDaggerExtension.scalarClassify.eq_1)
  pure ()

theorem DaggerFiniteDaggerExtension.scalarClassify_left.{u} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 29656 :=
  @(recovered_finite_private_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 30670)

noncomputable def DaggerFiniteDaggerExtension.orderedPosition.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 30837
        []}
    (arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 30837
        [arg0])
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 30837
        [arg0, arg1])
    :
    recovered_closed_result_type%
      DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 30837
      [arg0, arg1, arg2]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 30837 :=
    @(recovered_finite_private_expr%
      DaggerRecoveredFiniteRelativeCellFoundationData.jsonData 31094)
  exact @f arg0 arg1 arg2

