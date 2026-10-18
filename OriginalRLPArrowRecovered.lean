import Mathlib.CategoryTheory.ComposableArrows.Basic
import Mathlib.CategoryTheory.Category.ULift
import Mathlib.CategoryTheory.Presentable.Presheaf
import Mathlib.CategoryTheory.Presentable.Adjunction
import OriginalSmithLimitsRecovered
import OriginalRecoveredClosedExpression
import OriginalRecoveredRLPArrowExpressionData

/-! Original RLPArrow, rechecked using ordinary kernel validation. -/

set_option autoImplicit false
set_option maxRecDepth 100000
open CategoryTheory

theorem DaggerRLPAccessibility.arrowToChain._proof_1.{u_1, u_2} :
  recovered_closed_expr% DaggerRecoveredRLPArrowExpressionData.jsonData 3963 :=
  @(recovered_closed_expr% DaggerRecoveredRLPArrowExpressionData.jsonData 3983)

theorem DaggerRLPAccessibility.arrowToChain._proof_2.{u_1, u_2} :
  recovered_closed_expr% DaggerRecoveredRLPArrowExpressionData.jsonData 989 :=
  @(recovered_closed_expr% DaggerRecoveredRLPArrowExpressionData.jsonData 1008)

theorem DaggerRLPAccessibility.arrowToChain._proof_3.{u_1, u_2} :
  recovered_closed_expr% DaggerRecoveredRLPArrowExpressionData.jsonData 1607 :=
  @(recovered_closed_expr% DaggerRecoveredRLPArrowExpressionData.jsonData 1649)

theorem DaggerRLPAccessibility.arrowToChain._proof_4.{u_1, u_2} :
  recovered_closed_expr% DaggerRecoveredRLPArrowExpressionData.jsonData 3993 :=
  @(recovered_closed_expr% DaggerRecoveredRLPArrowExpressionData.jsonData 4000)

theorem DaggerRLPAccessibility.arrowToChain._proof_5.{u_1, u_2} :
  recovered_closed_expr% DaggerRecoveredRLPArrowExpressionData.jsonData 3784 :=
  @(recovered_closed_expr% DaggerRecoveredRLPArrowExpressionData.jsonData 3914)

noncomputable def DaggerRLPAccessibility.arrowToChain.{v, u}
    (C : Type u) [category : Category.{v} C] :
    Arrow C ⥤ ComposableArrows C 1 := by
  let f : recovered_closed_expr% DaggerRecoveredRLPArrowExpressionData.jsonData 1801 :=
    @(recovered_closed_expr% DaggerRecoveredRLPArrowExpressionData.jsonData 1803)
  exact @f C category

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerRLPAccessibility.arrowToChain.eq_1)
  pure ()

theorem DaggerRLPAccessibility.chainToArrow._proof_1 :
  recovered_closed_expr% DaggerRecoveredRLPArrowExpressionData.jsonData 1875 :=
  @(recovered_closed_expr% DaggerRecoveredRLPArrowExpressionData.jsonData 520)

theorem DaggerRLPAccessibility.chainToArrow._proof_2 :
  recovered_closed_expr% DaggerRecoveredRLPArrowExpressionData.jsonData 603 :=
  @(recovered_closed_expr% DaggerRecoveredRLPArrowExpressionData.jsonData 634)

theorem DaggerRLPAccessibility.chainToArrow._proof_3.{u_1, u_2} :
  recovered_closed_expr% DaggerRecoveredRLPArrowExpressionData.jsonData 736 :=
  @(recovered_closed_expr% DaggerRecoveredRLPArrowExpressionData.jsonData 783)

theorem DaggerRLPAccessibility.chainToArrow._proof_4.{u_1, u_2} :
  recovered_closed_expr% DaggerRecoveredRLPArrowExpressionData.jsonData 1911 :=
  @(recovered_closed_expr% DaggerRecoveredRLPArrowExpressionData.jsonData 1944)

theorem DaggerRLPAccessibility.chainToArrow._proof_5.{u_1, u_2} :
  recovered_closed_expr% DaggerRecoveredRLPArrowExpressionData.jsonData 4031 :=
  @(recovered_closed_expr% DaggerRecoveredRLPArrowExpressionData.jsonData 4063)

theorem DaggerRLPAccessibility.chainToArrow._proof_6.{u_1, u_2} :
  recovered_closed_expr% DaggerRecoveredRLPArrowExpressionData.jsonData 1744 :=
  @(recovered_closed_expr% DaggerRecoveredRLPArrowExpressionData.jsonData 1786)

theorem DaggerRLPAccessibility.chainToArrow._proof_7.{u_1, u_2} :
  recovered_closed_expr% DaggerRecoveredRLPArrowExpressionData.jsonData 2615 :=
  @(recovered_closed_expr% DaggerRecoveredRLPArrowExpressionData.jsonData 2749)

noncomputable def DaggerRLPAccessibility.chainToArrow.{v, u}
    (C : Type u) [category : Category.{v} C] :
    ComposableArrows C 1 ⥤ Arrow C := by
  let f : recovered_closed_expr% DaggerRecoveredRLPArrowExpressionData.jsonData 246 :=
    @(recovered_closed_expr% DaggerRecoveredRLPArrowExpressionData.jsonData 362)
  exact @f C category

theorem DaggerRLPAccessibility.arrowCounit._proof_1 :
  recovered_closed_expr% DaggerRecoveredRLPArrowExpressionData.jsonData 378 :=
  @(recovered_closed_expr% DaggerRecoveredRLPArrowExpressionData.jsonData 384)

theorem DaggerRLPAccessibility.arrowCounit._proof_2.{u_1, u_2} :
  recovered_closed_expr% DaggerRecoveredRLPArrowExpressionData.jsonData 2055 :=
  @(recovered_closed_expr% DaggerRecoveredRLPArrowExpressionData.jsonData 2101)

theorem DaggerRLPAccessibility.arrowCounit._proof_3.{u_1, u_2} :
  recovered_closed_expr% DaggerRecoveredRLPArrowExpressionData.jsonData 2215 :=
  @(recovered_closed_expr% DaggerRecoveredRLPArrowExpressionData.jsonData 2487)

noncomputable def DaggerRLPAccessibility.arrowCounit.{v, u} :
  recovered_closed_expr% DaggerRecoveredRLPArrowExpressionData.jsonData 413 :=
  @(recovered_closed_expr% DaggerRecoveredRLPArrowExpressionData.jsonData 483)

theorem DaggerRLPAccessibility.arrowToChain_map_right.{v, u} :
  recovered_closed_expr% DaggerRecoveredRLPArrowExpressionData.jsonData 550 :=
  @(recovered_closed_expr% DaggerRecoveredRLPArrowExpressionData.jsonData 558)

theorem DaggerRLPAccessibility.arrowToChain_obj_hom.{v, u} :
  recovered_closed_expr% DaggerRecoveredRLPArrowExpressionData.jsonData 581 :=
  @(recovered_closed_expr% DaggerRecoveredRLPArrowExpressionData.jsonData 586)

theorem DaggerRLPAccessibility.arrowUnit._proof_1.{u_1, u_2} :
  recovered_closed_expr% DaggerRecoveredRLPArrowExpressionData.jsonData 1825 :=
  @(recovered_closed_expr% DaggerRecoveredRLPArrowExpressionData.jsonData 1874)

theorem DaggerRLPAccessibility.arrowUnit._proof_2.{u_1, u_2} :
  recovered_closed_expr% DaggerRecoveredRLPArrowExpressionData.jsonData 2872 :=
  @(recovered_closed_expr% DaggerRecoveredRLPArrowExpressionData.jsonData 3121)

noncomputable def DaggerRLPAccessibility.arrowUnit.{v, u} :
  recovered_closed_expr% DaggerRecoveredRLPArrowExpressionData.jsonData 805 :=
  @(recovered_closed_expr% DaggerRecoveredRLPArrowExpressionData.jsonData 851)

theorem DaggerRLPAccessibility.arrowToChain_map_left.{v, u} :
  recovered_closed_expr% DaggerRecoveredRLPArrowExpressionData.jsonData 866 :=
  @(recovered_closed_expr% DaggerRecoveredRLPArrowExpressionData.jsonData 873)

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `CategoryTheory.Arrow.isoMk.congr_simp)
  pure ()

theorem DaggerRLPAccessibility.arrowToChain_obj_left.{v, u} :
  recovered_closed_expr% DaggerRecoveredRLPArrowExpressionData.jsonData 1793 :=
  @(recovered_closed_expr% DaggerRecoveredRLPArrowExpressionData.jsonData 1799)

theorem DaggerRLPAccessibility.arrowToChain_obj_right.{v, u} :
  recovered_closed_expr% DaggerRecoveredRLPArrowExpressionData.jsonData 1949 :=
  @(recovered_closed_expr% DaggerRecoveredRLPArrowExpressionData.jsonData 1953)

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerRLPAccessibility.chainToArrow.eq_1)
  pure ()

theorem DaggerRLPAccessibility.chainToArrow_map_left.{v, u} :
  recovered_closed_expr% DaggerRecoveredRLPArrowExpressionData.jsonData 1995 :=
  @(recovered_closed_expr% DaggerRecoveredRLPArrowExpressionData.jsonData 2002)

noncomputable def DaggerRLPAccessibility.arrowEquivalence.{v, u} :
  recovered_closed_expr% DaggerRecoveredRLPArrowExpressionData.jsonData 2494 :=
  @(recovered_closed_expr% DaggerRecoveredRLPArrowExpressionData.jsonData 2511)

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `CategoryTheory.ComposableArrows.isoMk₁.congr_simp)
  pure ()

noncomputable def DaggerRLPAccessibility.arrowSmallEquivalence.{w, v, u} :
  recovered_closed_expr% DaggerRecoveredRLPArrowExpressionData.jsonData 4087 :=
  @(recovered_closed_expr% DaggerRecoveredRLPArrowExpressionData.jsonData 4130)

theorem DaggerRLPAccessibility.arrowLocallyPresentable.{w, v, u} :
  recovered_closed_expr% DaggerRecoveredRLPArrowExpressionData.jsonData 4139 :=
  @(recovered_closed_expr% DaggerRecoveredRLPArrowExpressionData.jsonData 4268)

theorem DaggerRLPAccessibility.chainToArrow_map_right.{v, u} :
  recovered_closed_expr% DaggerRecoveredRLPArrowExpressionData.jsonData 4284 :=
  @(recovered_closed_expr% DaggerRecoveredRLPArrowExpressionData.jsonData 4291)

