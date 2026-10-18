import OriginalICellGeneratorsRecovered
import CoproductCellSerialization
import OriginalCofibrationSOARecovered
import OriginalRecoveredClosedExpressionApplication
import OriginalRecoveredGlobalLeftProperData

/-! Original ICellClosure, with unchanged closed types and values. -/

set_option autoImplicit false
set_option maxRecDepth 100000

noncomputable abbrev DaggerICellLocalComparison.I.{u}
    :
    recovered_closed_result_type%
      DaggerRecoveredGlobalLeftProperData.jsonData 5622
      []
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 5622 :=
    @(recovered_closed_expr%
      DaggerRecoveredGlobalLeftProperData.jsonData 187226)
  exact @f

noncomputable abbrev DaggerICellLocalComparison.ICell.{u}
    :
    recovered_closed_result_type%
      DaggerRecoveredGlobalLeftProperData.jsonData 7737
      []
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 7737 :=
    @(recovered_closed_expr%
      DaggerRecoveredGlobalLeftProperData.jsonData 190198)
  exact @f

theorem DaggerICellLocalComparison.instHasColimitsG_iCellClosure.{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 18603 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 12787)

theorem DaggerICellLocalComparison.batches_le_U.{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 189851 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 189870)

theorem DaggerICellLocalComparison.ICell_le_U.{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 189239 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 189272)

theorem DaggerICellLocalComparison.original_cofan_mem_U.{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 189433 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 189527)

theorem DaggerICellLocalComparison.soaUniversalData._proof_1.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 189548 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 189550)

noncomputable def DaggerICellLocalComparison.icellData.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 189770
        []}
    [arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 189770
        [arg0]]
    [arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 189770
        [arg0, arg1]]
    [arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 189770
        [arg0, arg1, arg2]]
    [arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 189770
        [arg0, arg1, arg2, arg3]]
    {arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 189770
        [arg0, arg1, arg2, arg3, arg4]}
    {arg6 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 189770
        [arg0, arg1, arg2, arg3, arg4, arg5]}
    {arg7 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 189770
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6]}
    (arg8 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 189770
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7])
    :
    recovered_closed_result_type%
      DaggerRecoveredGlobalLeftProperData.jsonData 189770
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 189770 :=
    @(recovered_closed_expr%
      DaggerRecoveredGlobalLeftProperData.jsonData 189791)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5 arg6 arg7 arg8

theorem DaggerICellLocalComparison.soaUniversalData._proof_2.{u_1} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 190313 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 190351)

noncomputable def DaggerICellLocalComparison.soaUniversalData.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 189561
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 189561
        [arg0]}
    (arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredGlobalLeftProperData.jsonData 189561
        [arg0, arg1])
    :
    recovered_closed_result_type%
      DaggerRecoveredGlobalLeftProperData.jsonData 189561
      [arg0, arg1, arg2]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 189561 :=
    @(recovered_closed_expr%
      DaggerRecoveredGlobalLeftProperData.jsonData 189616)
  exact @f arg0 arg1 arg2

theorem DaggerICellLocalComparison.soaUniversalData_fac.{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 189740 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 189752)

theorem DaggerICellLocalComparison.soaUniversalData_original.{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 189821 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 189826)

theorem DaggerICellLocalComparison.icell_embedding.{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 189836 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 189849)

theorem DaggerICellLocalComparison.soa_original_factorization.{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 189873 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 189876)

theorem DaggerICellLocalComparison.icellData_original.{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 189924 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 189935)

theorem DaggerICellLocalComparison.relativeCell_mem.{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 189975 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 190077)

theorem DaggerICellLocalComparison.icell_cobase_embedding.{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 190091 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 190116)

theorem DaggerICellLocalComparison.soa_mem_ICell.{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 190203 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 190216)

theorem DaggerICellLocalComparison.soa_embedding.{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 190122 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 190134)

theorem DaggerICellLocalComparison.icell_local_comparison.{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 190357 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 190383)

theorem DaggerICellLocalComparison.soa_local_comparison.{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 190167 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 190195)

theorem DaggerICellLocalComparison.instFactIsRegularSoaCardinal_iCellClosure.{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 188556 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 187846)

theorem DaggerICellLocalComparison.transfinite_original_local.{u} :
  recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 190401 :=
  @(recovered_closed_expr%
    DaggerRecoveredGlobalLeftProperData.jsonData 190442)

