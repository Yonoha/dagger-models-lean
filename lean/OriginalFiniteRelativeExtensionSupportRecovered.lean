import OriginalFiniteRelativeExtensionTransferRecovered
import TopCatModelCategory.SSet.FactorThruFinite
import OriginalRecoveredClosedExpressionApplication
import OriginalRecoveredFiniteRelativeExtensionData

/-! Original FiniteRelativeExtensionSupport, with unchanged closed types and values. -/

set_option autoImplicit false
set_option maxRecDepth 100000

noncomputable def DaggerFiniteRelativeExtension.extensionSubcomplex.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 6307
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 6307
        [arg0]}
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 6307
        [arg0, arg1])
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 6307
        [arg0, arg1, arg2])
    :
    recovered_closed_result_type%
      DaggerRecoveredFiniteRelativeExtensionData.jsonData 6307
      [arg0, arg1, arg2, arg3]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 6307 :=
    @(recovered_closed_expr%
      DaggerRecoveredFiniteRelativeExtensionData.jsonData 6328)
  exact @f arg0 arg1 arg2 arg3

theorem DaggerFiniteRelativeExtension.extensionInclusion._proof_1.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 5598 :=
  @(recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 5607)

noncomputable def DaggerFiniteRelativeExtension.extensionInclusion.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 5612
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 5612
        [arg0]}
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 5612
        [arg0, arg1])
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 5612
        [arg0, arg1, arg2])
    :
    recovered_closed_result_type%
      DaggerRecoveredFiniteRelativeExtensionData.jsonData 5612
      [arg0, arg1, arg2, arg3]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 5612 :=
    @(recovered_closed_expr%
      DaggerRecoveredFiniteRelativeExtensionData.jsonData 5637)
  exact @f arg0 arg1 arg2 arg3

theorem DaggerFiniteRelativeExtension.range_extensionInclusion_iff.{u} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 5716 :=
  @(recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 5959)

theorem DaggerFiniteRelativeExtension.complementToFinite._proof_1.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 5218 :=
  @(recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 5446)

noncomputable def DaggerFiniteRelativeExtension.complementToFinite.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 6079
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 6079
        [arg0]}
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 6079
        [arg0, arg1])
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 6079
        [arg0, arg1, arg2])
    (arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredFiniteRelativeExtensionData.jsonData 6079
        [arg0, arg1, arg2, arg3])
    :
    recovered_closed_result_type%
      DaggerRecoveredFiniteRelativeExtensionData.jsonData 6079
      [arg0, arg1, arg2, arg3, arg4]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 6079 :=
    @(recovered_closed_expr%
      DaggerRecoveredFiniteRelativeExtensionData.jsonData 6084)
  exact @f arg0 arg1 arg2 arg3 arg4

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerFiniteRelativeExtension.complementToFinite.eq_1)
  pure ()

theorem DaggerFiniteRelativeExtension.extensionInclusion_ι.{u} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 5556 :=
  @(recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 5563)

theorem DaggerFiniteRelativeExtension.extensionInclusion_ι_assoc.{u} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 5982 :=
  @(recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 6043)

theorem DaggerFiniteRelativeExtension.complementToFinite_injective.{u} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 6096 :=
  @(recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 6302)

theorem DaggerFiniteRelativeExtension.finite_added_extension.{u} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 6055 :=
  @(recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 6074)

theorem DaggerFiniteRelativeExtension.instMonoSSetExtensionInclusion.{u} :
  recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 6339 :=
  @(recovered_closed_expr%
    DaggerRecoveredFiniteRelativeExtensionData.jsonData 6388)
attribute [instance] DaggerFiniteRelativeExtension.instMonoSSetExtensionInclusion

