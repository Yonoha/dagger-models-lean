import FixedCategoryColimits
import FixedGraphConnectedColimits
import FixedCategoryHomLimits
import Mathlib.Data.Countable.Small
import Mathlib.CategoryTheory.EssentiallySmall
import Mathlib.AlgebraicTopology.SimplicialSet.Finite
import Mathlib.Data.Countable.Basic
import Mathlib.Logic.Equiv.List
import Mathlib.CategoryTheory.Limits.Types.Colimits
import OriginalRecoveredClosedExpressionApplication
import OriginalRecoveredUnitaryPrivateExpression
import OriginalRecoveredUnitaryModelFoundationData

/-! Original UnitaryIntervalCountability, with unchanged closed types and values. -/

set_option autoImplicit false
set_option maxRecDepth 100000


namespace DaggerUnitaryInterval
universe u
open CategoryTheory

noncomputable def pathCode (G : DaggerModels.DaggerSimplicialGraph.{u})
    (n : SimplexCategoryᵒᵖ) {x y : G.Obj} (p : DaggerModels.FreeSimplicialPaths.Path G n x y) :
    List (Σ a, Σ b, (G.Hom a b).obj n) :=
  match p with
  | .nil => []
  | .cons q e => ⟨_, _, e⟩ :: pathCode G n q

end DaggerUnitaryInterval

theorem DaggerUnitaryInterval.pathCode_injective.{u} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 6309 :=
  @(recovered_unitary_private_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 7779)

theorem DaggerUnitaryInterval.countable_paths.{u} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 5903 :=
  @(recovered_unitary_private_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 5960)

noncomputable def DaggerUnitaryInterval.CountableHoms.{u}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryModelFoundationData.jsonData 8326
        []}
    (arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryModelFoundationData.jsonData 8326
        [arg0])
    :
    recovered_closed_result_type%
      DaggerRecoveredUnitaryModelFoundationData.jsonData 8326
      [arg0, arg1]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 8326 :=
    @(recovered_unitary_private_expr%
      DaggerRecoveredUnitaryModelFoundationData.jsonData 8341)
  exact @f arg0 arg1

noncomputable abbrev DaggerUnitaryInterval.countable_graph_colimit.match_1_1.{u_1, u_2}
    {arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryModelFoundationData.jsonData 8150
        []}
    {arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryModelFoundationData.jsonData 8150
        [arg0]}
    [arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryModelFoundationData.jsonData 8150
        [arg0, arg1]]
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryModelFoundationData.jsonData 8150
        [arg0, arg1, arg2])
    (arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryModelFoundationData.jsonData 8150
        [arg0, arg1, arg2, arg3])
    (arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryModelFoundationData.jsonData 8150
        [arg0, arg1, arg2, arg3, arg4])
    (arg6 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryModelFoundationData.jsonData 8150
        [arg0, arg1, arg2, arg3, arg4, arg5])
    (arg7 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryModelFoundationData.jsonData 8150
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6])
    (arg8 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryModelFoundationData.jsonData 8150
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7])
    (arg9 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryModelFoundationData.jsonData 8150
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8])
    :
    recovered_closed_result_type%
      DaggerRecoveredUnitaryModelFoundationData.jsonData 8150
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 8150 :=
    @(recovered_unitary_private_expr%
      DaggerRecoveredUnitaryModelFoundationData.jsonData 8188)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5 arg6 arg7 arg8 arg9

theorem DaggerUnitaryInterval.countable_graph_colimit.{u} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 8524 :=
  @(recovered_unitary_private_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 9194)

theorem DaggerUnitaryInterval.countable_of_iso.{u} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 11978 :=
  @(recovered_unitary_private_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 12051)

theorem DaggerUnitaryInterval.countable_small_colimit.{u} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 9352 :=
  @(recovered_unitary_private_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 9565)

theorem DaggerUnitaryInterval.countable_colimit.{u, v, w} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 7835 :=
  @(recovered_unitary_private_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 8052)

noncomputable abbrev DaggerRecoveredUnitaryPrivate.pathCodeSplitter.{u_1, u_2}
    (arg0 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryModelFoundationData.jsonData 8264
        [])
    (arg1 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryModelFoundationData.jsonData 8264
        [arg0])
    {arg2 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryModelFoundationData.jsonData 8264
        [arg0, arg1]}
    (arg3 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryModelFoundationData.jsonData 8264
        [arg0, arg1, arg2])
    (arg4 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryModelFoundationData.jsonData 8264
        [arg0, arg1, arg2, arg3])
    (arg5 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryModelFoundationData.jsonData 8264
        [arg0, arg1, arg2, arg3, arg4])
    (arg6 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryModelFoundationData.jsonData 8264
        [arg0, arg1, arg2, arg3, arg4, arg5])
    (arg7 :
      recovered_closed_binder_type%
        DaggerRecoveredUnitaryModelFoundationData.jsonData 8264
        [arg0, arg1, arg2, arg3, arg4, arg5, arg6])
    :
    recovered_closed_result_type%
      DaggerRecoveredUnitaryModelFoundationData.jsonData 8264
      [arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7]
    := by
  let f : recovered_closed_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 8264 :=
    @(recovered_unitary_private_expr%
      DaggerRecoveredUnitaryModelFoundationData.jsonData 8265)
  exact @f arg0 arg1 arg2 arg3 arg4 arg5 arg6 arg7

theorem DaggerUnitaryInterval.countable_isColimit.{u, v, w} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 8382 :=
  @(recovered_unitary_private_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 8456)

theorem DaggerRecoveredUnitaryPrivate.pathCodeEq2.{u_1, u_2} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 9295 :=
  @(recovered_unitary_private_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 9308)

theorem DaggerRecoveredUnitaryPrivate.pathCodeEq1.{u_1, u_2} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 9620 :=
  @(recovered_unitary_private_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 9628)

theorem DaggerUnitaryInterval.countable_sSetHom.{u} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 9641 :=
  @(recovered_unitary_private_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 10274)

theorem DaggerUnitaryInterval.countable_of_isPushout.{u} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 12117 :=
  @(recovered_unitary_private_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 12339)

theorem DaggerUnitaryInterval.countable_graphHom.{u} :
  recovered_closed_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 12377 :=
  @(recovered_unitary_private_expr%
    DaggerRecoveredUnitaryModelFoundationData.jsonData 12483)

