import OriginalTransfiniteEmbeddingsRecovered
import OriginalActualCoherentUnitaryIdentityRecovered
import OriginalActualGlobalWeakDefinitionsRecovered
import OriginalActualGlobalWeakPropertiesRecovered
import Mathlib.CategoryTheory.MorphismProperty.Limits
import OriginalRecoveredClosedExpressionApplication
import OriginalRecoveredGlobalLeftProperData

/-! Original ICellUniversal, with unchanged closed types and values. -/

set_option autoImplicit false
set_option maxRecDepth 100000

noncomputable abbrev DaggerICellLocalComparison.G.{u}
    :
    recovered_closed_result_type%
      DaggerRecoveredGlobalLeftProperData.jsonData 8279
      []
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 8279 :=
    @(recovered_closed_expr%
      DaggerRecoveredGlobalLeftProperData.jsonData 57)
  exact @f

noncomputable def DaggerICellLocalComparison.UniversalCobase.{v, w}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 8344
        []}
    [arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 8344
        [arg0]]
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 8344
        [arg0, arg1])
    :
    recovered_closed_result_type%
      DaggerRecoveredGlobalLeftProperData.jsonData 8344
      [arg0, arg1, arg2]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 8344 :=
    @(recovered_closed_expr%
      DaggerRecoveredGlobalLeftProperData.jsonData 8347)
  exact @f arg0 arg1 arg2

noncomputable abbrev DaggerICellLocalComparison.Emb.{u}
    :
    recovered_closed_result_type%
      DaggerRecoveredGlobalLeftProperData.jsonData 7737
      []
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 7737 :=
    @(recovered_closed_expr%
      DaggerRecoveredGlobalLeftProperData.jsonData 3738)
  exact @f

noncomputable abbrev DaggerICellLocalComparison.LocalGW.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 8282
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 8282
        [arg0]}
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 8282
        [arg0, arg1])
    :
    recovered_closed_result_type%
      DaggerRecoveredGlobalLeftProperData.jsonData 8282
      [arg0, arg1, arg2]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 8282 :=
    @(recovered_closed_expr%
      DaggerRecoveredGlobalLeftProperData.jsonData 8289)
  exact @f arg0 arg1 arg2

noncomputable def DaggerICellLocalComparison.BaseLocal.{u}
    :
    recovered_closed_result_type%
      DaggerRecoveredGlobalLeftProperData.jsonData 7737
      []
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 7737 :=
    @(recovered_closed_expr%
      DaggerRecoveredGlobalLeftProperData.jsonData 8096)
  exact @f

noncomputable def DaggerICellLocalComparison.U.{u}
    :
    recovered_closed_result_type%
      DaggerRecoveredGlobalLeftProperData.jsonData 7737
      []
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 7737 :=
    @(recovered_closed_expr%
      DaggerRecoveredGlobalLeftProperData.jsonData 8132)
  exact @f

theorem DaggerICellLocalComparison.universalCobase_stable.{v, w} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 8244 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 8278)
attribute [instance] DaggerICellLocalComparison.universalCobase_stable

theorem DaggerICellLocalComparison.U_cobase_stable.{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 7729 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 7762)
attribute [instance] DaggerICellLocalComparison.U_cobase_stable

theorem DaggerICellLocalComparison.universalCobase_iff.{v, w} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 7840 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 8061)

theorem DaggerICellLocalComparison.U_respectsIso.{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 8100 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 8108)
attribute [instance] DaggerICellLocalComparison.U_respectsIso

theorem DaggerICellLocalComparison.universalCobase_le.{v, w} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 8758 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 8790)

theorem DaggerICellLocalComparison.U_le_Emb.{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 8125 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 8146)

theorem DaggerICellLocalComparison.U_le_BaseLocal.{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 8667 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 8675)

theorem DaggerICellLocalComparison.U_of_pushout.{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 8314 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 8339)

theorem DaggerICellLocalComparison.U_original_local.{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 8193 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 8233)

noncomputable def DaggerICellLocalComparison.UEmb.{u}
    :
    recovered_closed_result_type%
      DaggerRecoveredGlobalLeftProperData.jsonData 7737
      []
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 7737 :=
    @(recovered_closed_expr%
      DaggerRecoveredGlobalLeftProperData.jsonData 8234)
  exact @f

theorem DaggerICellLocalComparison.U_original_iff.{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 8404 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 8414)

theorem DaggerICellLocalComparison.universalCobase_inf.{v, w} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 8456 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 8599)

noncomputable def DaggerICellLocalComparison.ULocal.{u}
    :
    recovered_closed_result_type%
      DaggerRecoveredGlobalLeftProperData.jsonData 7737
      []
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 7737 :=
    @(recovered_closed_expr%
      DaggerRecoveredGlobalLeftProperData.jsonData 8600)
  exact @f

theorem DaggerICellLocalComparison.U_iff.{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 8614 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 8666)

theorem DaggerICellLocalComparison.U_original_emb.{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 8688 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 8713)

theorem DaggerICellLocalComparison.universalCobase_respectsIso.{v, w} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 8720 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 8734)
attribute [instance] DaggerICellLocalComparison.universalCobase_respectsIso

