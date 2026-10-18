import NativeReedyFibrantHorizontalMapping

/-! Genuine Reedy fibrations are Kan fibrations on every ORIGINAL row. -/
set_option autoImplicit false
open CategoryTheory Limits HomotopicalAlgebra Simplicial Opposite
open DaggerNativeBisimplicialHorizontalMapping DaggerNativeBisimplicialReedyRestrictions
open DaggerNativeReedyFibrantHorizontalMapping
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeReedyRowFibrations
noncomputable section

theorem mapping_empty_isIso {X Y : BiSSet.{u}} (f : X ⟶ Y) :
    IsIso (horizontalMap empty f) := by
  let hX := mappingEmpty_isTerminal X
  let hY := mappingEmpty_isTerminal Y
  let e : horizontalMapping empty X ≅ horizontalMapping empty Y :=
    { hom := horizontalMap empty f
      inv := hX.from _
      hom_inv_id := hX.hom_ext _ _
      inv_hom_id := hY.hom_ext _ _ }
  exact ⟨⟨e.inv, e.hom_inv_id, e.inv_hom_id⟩⟩

theorem mapping_fibration {X Y : BiSSet.{u}} (f : X ⟶ Y) (hf : ReedyFibration f)
    (K : SSet.{u}) : Fibration (horizontalMap K f) := by
  have : Mono (emptyTo K) := emptyTo_mono K
  have : Fibration (relativeRestriction (emptyTo K) f) :=
    DaggerNativeBisimplicialReedyRestrictions.restriction_fibration f hf _
  have : IsIso (horizontalMap empty f) := mapping_empty_isIso f
  have hp : Fibration (C := SSet.{u}) (relativeRestriction (emptyTo K) f ≫
      pullback.snd (horizontalMap empty f) (horizontalPre (emptyTo K) Y)) := inferInstance
  simpa only [relativeRestriction_snd] using hp

theorem row_fibration {X Y : BiSSet.{u}} (f : X ⟶ Y) (hf : ReedyFibration f)
    (h : SimplexCategoryᵒᵖ) : Fibration (f.app h) := by
  obtain ⟨h⟩ := h
  induction h using SimplexCategory.rec with | _ n =>
    have hp : Fibration (horizontalMap (Δ[n] : SSet.{u}) f) := mapping_fibration f hf _
    let e : Arrow.mk (horizontalMap (Δ[n] : SSet.{u}) f) ≅ Arrow.mk (f.app (op ⦋n⦌)) :=
      Arrow.isoMk (horizontalSimplexIso X n) (horizontalSimplexIso Y n)
        (by exact (horizontalSimplexIso_natural f n).symm)
    exact (fibration_iff _).mpr
      (((fibrations SSet.{u}).arrow_mk_iso_iff e).mp ((fibration_iff _).mp hp))

end
end DaggerNativeReedyRowFibrations
