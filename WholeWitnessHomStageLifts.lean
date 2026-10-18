import WholeWitnessTriangleStageLifts
import WholeWitnessInverseStageLifts

/-!
# Original arrow factorizations lift to full inverse-witness morphisms

The inverse map and every original chosen edge and triangle are preserved.
All source presentability assumptions are explicit and concern entire objects.
-/
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory Simplicial
open DaggerSimplexInverseWitnessCategory DaggerWholeWitnessSides
universe u v w
namespace DaggerWholeWitnessHomStageLifts

variable {C : Type w} [Category.{v} C] {J : Type u} [SmallCategory J]
  [HasColimitsOfShape J C] (R : C ⥤ SSet.{u}) [PreservesColimitsOfShape J R]

theorem lift_original_arrow_factor (κ : Cardinal.{u}) [Fact κ.IsRegular]
    [IsCardinalFiltered J κ] {F : J ⥤ Witness R} {c : Cocone F} (hc : IsColimit c)
    (X : Witness R) [IsCardinalPresentable (R.obj X.arrow.right) κ]
    (hX : ∀ b, IsCardinalPresentable (side R X b ⊗ Δ[1]) κ ∧
      IsCardinalPresentable (side R X b ⊗ Δ[2]) κ)
    (h : X ⟶ c.pt) {i : J} (a : X.arrow ⟶ (F.obj i).arrow)
    (hfac : a ≫ (c.ι.app i).square = h.square) :
    ∃ (j : J) (f : X ⟶ F.obj j), f ≫ c.ι.app j = h := by
  obtain ⟨j, t, ht⟩ := DaggerWholeWitnessInverseStageLifts.inverse_commutes_eventually
    R κ hc X h a hfac
  let b := a ≫ (F.map t).square
  have hb : b ≫ (c.ι.app j).square = h.square := by
    have hw := congrArg (fun f : F.obj i ⟶ c.pt ↦ f.square) (c.w t)
    change (F.map t).square ≫ (c.ι.app j).square = (c.ι.app i).square at hw
    exact (Category.assoc a _ _).trans ((congrArg (fun z ↦ a ≫ z) hw).trans hfac)
  obtain ⟨k, v, hv⟩ := DaggerWholeWitnessTriangleStageLifts.triangle_squares_eventually
    R κ hc X hX h b hb
  let q := b ≫ (F.map v).square
  have hq : R.map q.right ≫ (F.obj k).data.inv = X.data.inv ≫ R.map q.left := by
    change (R.map (b ≫ (F.map v).square).right) ≫ (F.obj k).data.inv =
      X.data.inv ≫ R.map (b ≫ (F.map v).square).left
    simp only [Arrow.comp_right, Arrow.comp_left, R.map_comp]
    rw [Category.assoc, (F.map v).inverse_commutes, ← Category.assoc, ht, Category.assoc]
  let f : X ⟶ F.obj k :=
    { square := q
      inverse_commutes := hq
      triangleLeft := hv false
      triangleRight := hv true }
  refine ⟨k, f, Hom.ext R ?_⟩
  have hw := congrArg (fun f : F.obj j ⟶ c.pt ↦ f.square) (c.w v)
  change (F.map v).square ≫ (c.ι.app k).square = (c.ι.app j).square at hw
  exact (Category.assoc b _ _).trans ((congrArg (fun z ↦ b ≫ z) hw).trans hb)

theorem hom_factors_of_isColimit (κ : Cardinal.{u}) [Fact κ.IsRegular]
    [IsCardinalFiltered J κ] {F : J ⥤ Witness R} {c : Cocone F} (hc : IsColimit c)
    (X : Witness R) [IsCardinalPresentable X.arrow κ]
    [IsCardinalPresentable (R.obj X.arrow.right) κ]
    (hX : ∀ b, IsCardinalPresentable (side R X b ⊗ Δ[1]) κ ∧
      IsCardinalPresentable (side R X b ⊗ Δ[2]) κ) (h : X ⟶ c.pt) :
    ∃ (j : J) (f : X ⟶ F.obj j), f ≫ c.ι.app j = h := by
  obtain ⟨i, a, ha⟩ := IsCardinalPresentable.exists_hom_of_isColimit κ
    (isColimitOfPreserves (forget R) hc) h.square
  exact lift_original_arrow_factor R κ hc X hX h a ha

end DaggerWholeWitnessHomStageLifts
