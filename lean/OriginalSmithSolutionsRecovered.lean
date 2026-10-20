import OriginalSmithCardinalRecovered
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import OriginalRecoveredClosedExpression
import OriginalRecoveredSmithSolutionExpressionData

/-! Original Smith solution-set generators, rechecked from preserved closed expressions. -/

set_option autoImplicit false
set_option maxRecDepth 100000
open CategoryTheory

section
universe w v u
namespace DaggerSmithSolutionSet

/-- The original small solution set factors every full arrow-category square. -/
structure SolutionData {C : Type u} [Category.{v} C] (I W : MorphismProperty C) where
  index : I.toSet → Type w
  arrow : (i : I.toSet) → index i → Arrow C
  weak : ∀ i s, W (arrow i s).hom
  factor : ∀ (i : I.toSet) (f : Arrow C), W f.hom → ∀ (φ : i.1 ⟶ f),
    ∃ (s : index i) (α : i.1 ⟶ arrow i s) (β : arrow i s ⟶ f), α ≫ β = φ

end DaggerSmithSolutionSet
end

theorem DaggerSmithSolutionSet.instHasColimitsOfSize_smithSolutions.{w, v, u} :
  recovered_closed_expr% DaggerRecoveredSmithSolutionExpressionData.jsonData 6992 :=
  @(recovered_closed_expr% DaggerRecoveredSmithSolutionExpressionData.jsonData 6999)
attribute [local instance] DaggerSmithSolutionSet.instHasColimitsOfSize_smithSolutions

theorem DaggerSmithSolutionSet.corner._proof_1.{u_1, u_2, u_3} :
  recovered_closed_expr% DaggerRecoveredSmithSolutionExpressionData.jsonData 7305 :=
  @(recovered_closed_expr% DaggerRecoveredSmithSolutionExpressionData.jsonData 7332)

theorem DaggerSmithSolutionSet.corner._proof_2.{u_1, u_2, u_3} :
  recovered_closed_expr% DaggerRecoveredSmithSolutionExpressionData.jsonData 7603 :=
  @(recovered_closed_expr% DaggerRecoveredSmithSolutionExpressionData.jsonData 7623)

noncomputable def DaggerSmithSolutionSet.corner.{w, v, u}
    {C : Type u} [category : Category.{v} C]
    [locallyPresentable : IsLocallyPresentable.{w} C] {I W : MorphismProperty C}
    (S : DaggerSmithSolutionSet.SolutionData.{w, v, u} I W)
    (i : I.toSet) (s : S.index i) (α : i.1 ⟶ S.arrow i s) :
    Limits.pushout α.left i.1.hom ⟶ (S.arrow i s).right := by
  let f : recovered_closed_expr% DaggerRecoveredSmithSolutionExpressionData.jsonData 2413 :=
    @(recovered_closed_expr% DaggerRecoveredSmithSolutionExpressionData.jsonData 2422)
  exact @f C category locallyPresentable I W S i s α

noncomputable def DaggerSmithSolutionSet.left.{w, v, u}
    {C : Type u} [category : Category.{v} C]
    [locallyPresentable : IsLocallyPresentable.{w} C] {I W : MorphismProperty C}
    [small : MorphismProperty.IsSmall.{w} I]
    (S : DaggerSmithSolutionSet.SolutionData.{w, v, u} I W)
    (i : I.toSet) (s : S.index i) (α : i.1 ⟶ S.arrow i s) :
    Limits.pushout α.left i.1.hom ⟶ (DaggerSmithSolutionSet.soaFactorization I).Z.obj
      (Arrow.mk (DaggerSmithSolutionSet.corner S i s α)) := by
  let f : recovered_closed_expr% DaggerRecoveredSmithSolutionExpressionData.jsonData 291 :=
    @(recovered_closed_expr% DaggerRecoveredSmithSolutionExpressionData.jsonData 330)
  exact @f C category locallyPresentable I W small S i s α

noncomputable def DaggerSmithSolutionSet.generator.{w, v, u}
    {C : Type u} [category : Category.{v} C]
    [locallyPresentable : IsLocallyPresentable.{w} C] {I W : MorphismProperty C}
    [small : MorphismProperty.IsSmall.{w} I]
    (S : DaggerSmithSolutionSet.SolutionData.{w, v, u} I W)
    (i : I.toSet) (s : S.index i) (α : i.1 ⟶ S.arrow i s) :
    (S.arrow i s).left ⟶ (DaggerSmithSolutionSet.soaFactorization I).Z.obj
      (Arrow.mk (DaggerSmithSolutionSet.corner S i s α)) := by
  let f : recovered_closed_expr% DaggerRecoveredSmithSolutionExpressionData.jsonData 952 :=
    @(recovered_closed_expr% DaggerRecoveredSmithSolutionExpressionData.jsonData 987)
  exact @f C category locallyPresentable I W small S i s α

noncomputable def DaggerSmithSolutionSet.right.{w, v, u}
    {C : Type u} [category : Category.{v} C]
    [locallyPresentable : IsLocallyPresentable.{w} C] {I W : MorphismProperty C}
    [small : MorphismProperty.IsSmall.{w} I]
    (S : DaggerSmithSolutionSet.SolutionData.{w, v, u} I W)
    (i : I.toSet) (s : S.index i) (α : i.1 ⟶ S.arrow i s) :
    (DaggerSmithSolutionSet.soaFactorization I).Z.obj
      (Arrow.mk (DaggerSmithSolutionSet.corner S i s α)) ⟶ (S.arrow i s).right := by
  let f : recovered_closed_expr% DaggerRecoveredSmithSolutionExpressionData.jsonData 2749 :=
    @(recovered_closed_expr% DaggerRecoveredSmithSolutionExpressionData.jsonData 2759)
  exact @f C category locallyPresentable I W small S i s α

theorem DaggerSmithSolutionSet.inl_corner.{w, v, u} :
  recovered_closed_expr% DaggerRecoveredSmithSolutionExpressionData.jsonData 2229 :=
  @(recovered_closed_expr% DaggerRecoveredSmithSolutionExpressionData.jsonData 2379)

theorem DaggerSmithSolutionSet.generator_right.{w, v, u} :
  recovered_closed_expr% DaggerRecoveredSmithSolutionExpressionData.jsonData 7346 :=
  @(recovered_closed_expr% DaggerRecoveredSmithSolutionExpressionData.jsonData 7434)

theorem DaggerSmithSolutionSet.generator_right_assoc.{w, v, u} :
  recovered_closed_expr% DaggerRecoveredSmithSolutionExpressionData.jsonData 679 :=
  @(recovered_closed_expr% DaggerRecoveredSmithSolutionExpressionData.jsonData 940)

noncomputable def DaggerSmithSolutionSet.SquareIndex.{w, v, u} :
  recovered_closed_expr% DaggerRecoveredSmithSolutionExpressionData.jsonData 1001 :=
  @(recovered_closed_expr% DaggerRecoveredSmithSolutionExpressionData.jsonData 1060)

theorem DaggerSmithSolutionSet.generator_weak.{w, v, u} :
  recovered_closed_expr% DaggerRecoveredSmithSolutionExpressionData.jsonData 1165 :=
  @(recovered_closed_expr% DaggerRecoveredSmithSolutionExpressionData.jsonData 1270)

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerSmithSolutionSet.corner.eq_1)
  pure ()

theorem DaggerSmithSolutionSet.instLocallySmall_smithSolutions.{w, v, u} :
  recovered_closed_expr% DaggerRecoveredSmithSolutionExpressionData.jsonData 2732 :=
  @(recovered_closed_expr% DaggerRecoveredSmithSolutionExpressionData.jsonData 2739)

theorem DaggerSmithSolutionSet.squareHomSmall.{w, v, u} :
  recovered_closed_expr% DaggerRecoveredSmithSolutionExpressionData.jsonData 5765 :=
  @(recovered_closed_expr% DaggerRecoveredSmithSolutionExpressionData.jsonData 5917)
attribute [instance] DaggerSmithSolutionSet.squareHomSmall

theorem DaggerSmithSolutionSet.instSmallSquareIndex.{w, v, u} :
  recovered_closed_expr% DaggerRecoveredSmithSolutionExpressionData.jsonData 7013 :=
  @(recovered_closed_expr% DaggerRecoveredSmithSolutionExpressionData.jsonData 7059)
attribute [instance] DaggerSmithSolutionSet.instSmallSquareIndex

noncomputable def DaggerSmithSolutionSet.Index.{w, v, u} :
  recovered_closed_expr% DaggerRecoveredSmithSolutionExpressionData.jsonData 7690 :=
  @(recovered_closed_expr% DaggerRecoveredSmithSolutionExpressionData.jsonData 7700)

noncomputable def DaggerSmithSolutionSet.indexEquiv.{w, v, u} :
  recovered_closed_expr% DaggerRecoveredSmithSolutionExpressionData.jsonData 7144 :=
  @(recovered_closed_expr% DaggerRecoveredSmithSolutionExpressionData.jsonData 7162)

theorem DaggerSmithSolutionSet.J._proof_1.{u_1, u_2, u_3} :
  recovered_closed_expr% DaggerRecoveredSmithSolutionExpressionData.jsonData 7920 :=
  @(recovered_closed_expr% DaggerRecoveredSmithSolutionExpressionData.jsonData 7946)

noncomputable def DaggerSmithSolutionSet.family.{w, v, u} :
  recovered_closed_expr% DaggerRecoveredSmithSolutionExpressionData.jsonData 6804 :=
  @(recovered_closed_expr% DaggerRecoveredSmithSolutionExpressionData.jsonData 6841)

noncomputable def DaggerSmithSolutionSet.J.{w, v, u}
    {C : Type u} [category : Category.{v} C]
    [locallyPresentable : IsLocallyPresentable.{w} C] {I W : MorphismProperty C}
    [small : MorphismProperty.IsSmall.{w} I]
    (S : DaggerSmithSolutionSet.SolutionData.{w, v, u} I W) :
    MorphismProperty C := by
  let f : recovered_closed_expr% DaggerRecoveredSmithSolutionExpressionData.jsonData 7112 :=
    @(recovered_closed_expr% DaggerRecoveredSmithSolutionExpressionData.jsonData 7135)
  exact @f C category locallyPresentable I W small S

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerSmithSolutionSet.J.eq_1)
  pure ()

theorem DaggerSmithSolutionSet.generator_mem.{w, v, u} :
  recovered_closed_expr% DaggerRecoveredSmithSolutionExpressionData.jsonData 1506 :=
  @(recovered_closed_expr% DaggerRecoveredSmithSolutionExpressionData.jsonData 2200)

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerSmithSolutionSet.left.eq_1)
  pure ()

theorem DaggerSmithSolutionSet.fromGenerator._proof_1.{u_1, u_2, u_3} :
  recovered_closed_expr% DaggerRecoveredSmithSolutionExpressionData.jsonData 6237 :=
  @(recovered_closed_expr% DaggerRecoveredSmithSolutionExpressionData.jsonData 6340)

noncomputable def DaggerSmithSolutionSet.fromGenerator.{w, v, u}
    {C : Type u} [category : Category.{v} C]
    [locallyPresentable : IsLocallyPresentable.{w} C] {I W : MorphismProperty C}
    [small : MorphismProperty.IsSmall.{w} I]
    (S : DaggerSmithSolutionSet.SolutionData.{w, v, u} I W)
    (i : I.toSet) (s : S.index i) (α : i.1 ⟶ S.arrow i s) :
    Arrow.mk (DaggerSmithSolutionSet.generator S i s α) ⟶ S.arrow i s := by
  let f : recovered_closed_expr% DaggerRecoveredSmithSolutionExpressionData.jsonData 7172 :=
    @(recovered_closed_expr% DaggerRecoveredSmithSolutionExpressionData.jsonData 7182)
  exact @f C category locallyPresentable I W small S i s α

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerSmithSolutionSet.fromGenerator.eq_1)
  pure ()

theorem DaggerSmithSolutionSet.inr_corner.{w, v, u} :
  recovered_closed_expr% DaggerRecoveredSmithSolutionExpressionData.jsonData 7637 :=
  @(recovered_closed_expr% DaggerRecoveredSmithSolutionExpressionData.jsonData 7683)

theorem DaggerSmithSolutionSet.inr_corner_assoc.{w, v, u} :
  recovered_closed_expr% DaggerRecoveredSmithSolutionExpressionData.jsonData 2578 :=
  @(recovered_closed_expr% DaggerRecoveredSmithSolutionExpressionData.jsonData 2689)

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerSmithSolutionSet.right.eq_1)
  pure ()

theorem DaggerSmithSolutionSet.generator_cof.{w, v, u} :
  recovered_closed_expr% DaggerRecoveredSmithSolutionExpressionData.jsonData 6909 :=
  @(recovered_closed_expr% DaggerRecoveredSmithSolutionExpressionData.jsonData 6986)

theorem DaggerSmithSolutionSet.J_le.{w, v, u} :
  recovered_closed_expr% DaggerRecoveredSmithSolutionExpressionData.jsonData 2816 :=
  @(recovered_closed_expr% DaggerRecoveredSmithSolutionExpressionData.jsonData 5755)

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerSmithSolutionSet.generator.eq_1)
  pure ()

theorem DaggerSmithSolutionSet.intoGenerator._proof_1.{u_1, u_2, u_3} :
  recovered_closed_expr% DaggerRecoveredSmithSolutionExpressionData.jsonData 8158 :=
  @(recovered_closed_expr% DaggerRecoveredSmithSolutionExpressionData.jsonData 8509)

noncomputable def DaggerSmithSolutionSet.intoGenerator.{w, v, u}
    {C : Type u} [category : Category.{v} C]
    [locallyPresentable : IsLocallyPresentable.{w} C] {I W : MorphismProperty C}
    [small : MorphismProperty.IsSmall.{w} I]
    (S : DaggerSmithSolutionSet.SolutionData.{w, v, u} I W)
    (i : I.toSet) (s : S.index i) (α : i.1 ⟶ S.arrow i s) :
    i.1 ⟶ Arrow.mk (DaggerSmithSolutionSet.generator S i s α) := by
  let f : recovered_closed_expr% DaggerRecoveredSmithSolutionExpressionData.jsonData 7070 :=
    @(recovered_closed_expr% DaggerRecoveredSmithSolutionExpressionData.jsonData 7101)
  exact @f C category locallyPresentable I W small S i s α

theorem DaggerSmithSolutionSet.square_factor.{w, v, u} :
  recovered_closed_expr% DaggerRecoveredSmithSolutionExpressionData.jsonData 6374 :=
  @(recovered_closed_expr% DaggerRecoveredSmithSolutionExpressionData.jsonData 6569)

theorem DaggerSmithSolutionSet.instIsSmallJ.{w, v, u} :
  recovered_closed_expr% DaggerRecoveredSmithSolutionExpressionData.jsonData 6858 :=
  @(recovered_closed_expr% DaggerRecoveredSmithSolutionExpressionData.jsonData 6896)
attribute [instance] DaggerSmithSolutionSet.instIsSmallJ

theorem DaggerSmithSolutionSet.inl_corner_assoc.{w, v, u} :
  recovered_closed_expr% DaggerRecoveredSmithSolutionExpressionData.jsonData 7980 :=
  @(recovered_closed_expr% DaggerRecoveredSmithSolutionExpressionData.jsonData 8055)

run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <|
    Lean.realizeGlobalConstNoOverload
      (Lean.mkIdent `DaggerSmithSolutionSet.intoGenerator.eq_1)
  pure ()

