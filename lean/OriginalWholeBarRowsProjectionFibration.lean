import OriginalBarRowsProjectionFibration
import OriginalWholeBarBisimplicial
import NativeBisimplicialCoproductRows
import NativeCoproductDescFibration

/-! The unchanged WHOLE original bar projection is a fibration on every row for Kan Homs. -/
set_option autoImplicit false
open CategoryTheory Limits HomotopicalAlgebra Simplicial Opposite DaggerModels
open DaggerOriginalBarRowsProjectionFibration DaggerOriginalSimplicialCategoryBarRows
open DaggerOriginalWholeBarBisimplicial DaggerNativeBisimplicialCoproductRows
open DaggerNativeCoproductDescFibration
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerOriginalWholeBarRowsProjectionFibration
noncomputable section

theorem whole_row_projection_square (C : SimplicialCat.{u, u}) (h : SimplexCategoryᵒᵖ) :
    (rowSigmaIso (barRows C) h).hom ≫ (wholeProjection C).app h =
      Limits.Sigma.desc (fun z ↦ (componentProjection C z).app h) := by
  apply Limits.Sigma.hom_ext
  intro z
  rw [← Category.assoc, rowSigmaIso_inclusion, Limits.Sigma.ι_desc]
  exact NatTrans.congr_app (Limits.Sigma.ι_desc (componentProjection C) z) h

theorem whole_row_projection_fibration (C : SimplicialCat.{u, u})
    [∀ x y : C.Obj, IsFibrant (C.enriched.Hom x y)] (h : SimplexCategoryᵒᵖ) :
    Fibration ((wholeProjection C).app h) := by
  have hz : ∀ z, Fibration ((componentProjection C z).app h) := by
    intro z
    obtain ⟨h⟩ := h
    induction h using SimplexCategory.rec with | _ k =>
      exact endpoint_row_projection_fibration C z k
  have hp : Fibration (Limits.Sigma.desc (fun z ↦ (componentProjection C z).app h)) :=
    sigma_desc_fibration _
  let e : Arrow.mk (Limits.Sigma.desc (fun z ↦ (componentProjection C z).app h)) ≅
      Arrow.mk ((wholeProjection C).app h) :=
    Arrow.isoMk (rowSigmaIso (barRows C) h) (Iso.refl _) (by
      change _ = _ ≫ 𝟙 _
      rw [Category.comp_id]
      exact whole_row_projection_square C h)
  exact (fibration_iff _).mpr
    (((fibrations SSet.{u}).arrow_mk_iso_iff e).mp ((fibration_iff _).mp hp))

end
end DaggerOriginalWholeBarRowsProjectionFibration
