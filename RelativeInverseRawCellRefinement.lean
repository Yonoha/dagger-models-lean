import RelativeInverseMapStageRefinement
import FiniteTensorSourcePresentability

/-! All eight actual chosen cells become compatible at a common later Arrow stage. -/
set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial MonoidalCategory
open DaggerNativeJoyalWeakSimplexInverse DaggerInverseTriangleCellFamily
open DaggerNativeEndomorphismSimplexMaps DaggerRectangularInverseWitnessData
open DaggerOriginalArrowWitnessStageDiagrams DaggerRelativeArrowStageFacs
universe u v w
namespace DaggerRelativeInverseRawCellRefinement

variable {C : Type w} [Category.{v} C] {J : Type u} [SmallCategory J]
  [HasColimitsOfShape J C] (R : C ⥤ SSet.{u}) [PreservesColimitsOfShape J R]
  {F : J ⥤ Arrow C} {c : Cocone F}

theorem exists_stage (κ : Cardinal.{u}) [Fact κ.IsRegular] [IsCardinalFiltered J κ]
    (hc : IsColimit c) (d : SimplexInverseData (R.map c.pt.hom))
    {i j k : J} (p : i ⟶ j) (q : j ⟶ k) (e : Data R (F.map p)) (f : Data R (F.map q))
    [IsCardinalPresentable (R.obj (F.obj i).left) κ]
    [IsCardinalPresentable (R.obj (F.obj i).right) κ]
    (heL : ∀ r : Kind, Square (R.map (c.ι.app i).left) (R.map (c.ι.app j).left)
      (DaggerRawIsoTriangleCells.cell e.left r) (DaggerRawIsoTriangleCells.cell d.left r))
    (heR : ∀ r : Kind, Square (R.map (c.ι.app i).right) (R.map (c.ι.app j).right)
      (DaggerRawIsoTriangleCells.cell e.right r) (DaggerRawIsoTriangleCells.cell d.right r))
    (hfL : ∀ r : Kind, Square (R.map (c.ι.app j).left) (R.map (c.ι.app k).left)
      (DaggerRawIsoTriangleCells.cell f.left r) (DaggerRawIsoTriangleCells.cell d.left r))
    (hfR : ∀ r : Kind, Square (R.map (c.ι.app j).right) (R.map (c.ι.app k).right)
      (DaggerRawIsoTriangleCells.cell f.right r) (DaggerRawIsoTriangleCells.cell d.right r)) :
    ∃ (l : J) (v : k ⟶ l),
      (∀ r : Kind, Square (R.map (F.map p).left) (R.map (F.map (q ≫ v)).left)
        (DaggerRawIsoTriangleCells.cell e.left r)
        (((ihom (R.obj (F.obj j).left)).map (R.map (F.map v).left)).app (op ⦋r.degree⦌)
          (DaggerRawIsoTriangleCells.cell f.left r))) ∧
      (∀ r : Kind, Square (R.map (F.map p).right) (R.map (F.map (q ≫ v)).right)
        (DaggerRawIsoTriangleCells.cell e.right r)
        (((ihom (R.obj (F.obj j).right)).map (R.map (F.map v).right)).app (op ⦋r.degree⦌)
          (DaggerRawIsoTriangleCells.cell f.right r))) := by
  let X : ULift.{u} (Bool × Kind) → SSet.{u} := fun a ↦
    match a.down.1 with
    | false => R.obj (F.obj i).left
    | true => R.obj (F.obj i).right
  let Y : ULift.{u} (Bool × Kind) → SSet.{u} := fun a ↦
    match a.down.1 with
    | false => R.obj (F.obj j).left
    | true => R.obj (F.obj j).right
  let D : ULift.{u} (Bool × Kind) → J ⥤ SSet.{u} := fun a ↦
    match a.down.1 with
    | false => leftDiagram R (F := F)
    | true => rightDiagram R (F := F)
  let cc : ∀ a, Cocone (D a) := fun a ↦
    match a with
    | ⟨(false, _)⟩ => leftCocone R (c := c)
    | ⟨(true, _)⟩ => rightCocone R (c := c)
  let pp : ∀ a, X a ⟶ Y a := fun a ↦
    match a with
    | ⟨(false, _)⟩ => R.map (F.map p).left
    | ⟨(true, _)⟩ => R.map (F.map p).right
  let s : ∀ a, ((ihom (X a)).obj ((D a).obj j)).obj (op ⦋a.down.2.degree⦌) := fun a ↦
    match a with
    | ⟨(false, r)⟩ => DaggerRawIsoTriangleCells.cell e.left r
    | ⟨(true, r)⟩ => DaggerRawIsoTriangleCells.cell e.right r
  let t : ∀ a, ((ihom (Y a)).obj ((D a).obj k)).obj (op ⦋a.down.2.degree⦌) := fun a ↦
    match a with
    | ⟨(false, r)⟩ => DaggerRawIsoTriangleCells.cell f.left r
    | ⟨(true, r)⟩ => DaggerRawIsoTriangleCells.cell f.right r
  have hcc : ∀ a, IsColimit (cc a) := by
    rintro ⟨⟨b, r⟩⟩
    cases b
    · exact leftIsColimit R hc
    · exact rightIsColimit R hc
  have hX : ∀ a, IsCardinalPresentable (X a ⊗ Δ[a.down.2.degree]) κ := by
    rintro ⟨⟨b, r⟩⟩
    have : IsCardinalPresentable (X ⟨(b, r)⟩) κ := by cases b <;> infer_instance
    exact DaggerFiniteTensorSourcePresentability.tensor_presentable κ _ _
  have heq : ∀ a,
      (simplexHomEquiv (X a) ((D a).obj j) a.down.2.degree (s a) ≫ (D a).map q) ≫
        (cc a).ι.app k =
      (pp a ▷ Δ[a.down.2.degree] ≫ simplexHomEquiv (Y a) ((D a).obj k) a.down.2.degree (t a)) ≫
        (cc a).ι.app k := by
    rintro ⟨⟨b, r⟩⟩
    cases b
    · exact DaggerRectangularCellStageRefinements.equation_after_colimit
        (R.map (F.map p).left) (R.map (c.ι.app i).left) (R.map (c.ι.app j).left)
        (left_leg_comp R c p) (R.map (F.map q).left)
        (R.map (c.ι.app j).left) (R.map (c.ι.app k).left) (left_leg_comp R c q)
        _ _ _ (heL r) (hfL r)
    · exact DaggerRectangularCellStageRefinements.equation_after_colimit
        (R.map (F.map p).right) (R.map (c.ι.app i).right) (R.map (c.ι.app j).right)
        (right_leg_comp R c p) (R.map (F.map q).right)
        (R.map (c.ι.app j).right) (R.map (c.ι.app k).right) (right_leg_comp R c q)
        _ _ _ (heR r) (hfR r)
  obtain ⟨l, v, hv⟩ := DaggerRectangularCellStageRefinements.finite_cells
    (A := ULift.{u} (Bool × Kind)) κ X Y
    (fun a : ULift.{u} (Bool × Kind) ↦ a.down.2.degree) D cc hcc hX q pp s t heq
  exact ⟨l, v, (fun r ↦ hv ⟨(false, r)⟩), (fun r ↦ hv ⟨(true, r)⟩)⟩

end DaggerRelativeInverseRawCellRefinement
