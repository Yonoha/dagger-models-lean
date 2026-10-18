import OriginalQuasicategoryInvertibleTriangles

/-!
# Actual ambient fillers of outer two-horns with original invertible edge images

Glue the original horn legs via Mathlib's actual pushout diagrams. Their shared
endpoint is retained literally. Original path cancellation gives the missing
triangle, and the two original coface equations verify the exact horn filler.
This interface is then applied to the original core inclusion.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerOriginalOrdinaryKanCoreEdgeMembership
open DaggerOriginalInnerHornFillers
open DaggerOriginalOrdinaryKanCoreKanInverseEdges
open DaggerOriginalQuasicategoryInvertibleTriangles

universe u

namespace DaggerOriginalQuasicategoryOuterTwoHorns

noncomputable section

/-- The right outer-horn first leg is the literal diagonal coface after inclusion. -/
theorem horn₂_inl_comp :
    SSet.horn₂₂.ι₀₂.{u} ≫ (Λ[2, 2] : (Δ[2] : SSet.{u}).Subcomplex).ι =
      SSet.stdSimplex.δ 1 := by
  simp [SSet.horn₂₂.ι₀₂]

/-- The right outer-horn second leg is the literal last-side coface after inclusion. -/
theorem horn₂_inr_comp :
    SSet.horn₂₂.ι₁₂.{u} ≫ (Λ[2, 2] : (Δ[2] : SSet.{u}).Subcomplex).ι =
      SSet.stdSimplex.δ 0 := by
  simp [SSet.horn₂₂.ι₁₂]

/-- Fill an actual left outer two-horn after mapping all its edges to original invertible edges. -/
theorem outer20_filling {X Z : SSet.{u}} (hX : innerHornFillers X) (f : Z ⟶ X)
    (hZ : ∀ e : Z.obj (op ⦋1⦌), edgeIsInvertible X (f.app (op ⦋1⦌) e))
    (σ₀ : (Λ[2, 0] : SSet.{u}) ⟶ Z) :
    ∃ σ : (Δ[2] : SSet.{u}) ⟶ X, σ₀ ≫ f = Λ[2, 0].ι ≫ σ := by
  let a : (Δ[1] : SSet.{u}) ⟶ Z := SSet.horn₂₀.ι₀₁ ≫ σ₀
  let b : (Δ[1] : SSet.{u}) ⟶ Z := SSet.horn₂₀.ι₀₂ ≫ σ₀
  have w : SSet.stdSimplex.δ 1 ≫ a = SSet.stdSimplex.δ 1 ≫ b := by
    change SSet.stdSimplex.δ 1 ≫ (SSet.horn₂₀.ι₀₁ ≫ σ₀) =
      SSet.stdSimplex.δ 1 ≫ (SSet.horn₂₀.ι₀₂ ≫ σ₀)
    rw [← Category.assoc, ← Category.assoc, SSet.horn₂₀.isPushout.w]
  have w₀ : Z.δ 1 (SSet.yonedaEquiv a) = Z.δ 1 (SSet.yonedaEquiv b) := by
    simpa only [yonedaEquiv_coface] using congrArg SSet.yonedaEquiv w
  let e : SSet.Edge (Z.δ 1 (SSet.yonedaEquiv a)) (Z.δ 0 (SSet.yonedaEquiv a)) :=
    SSet.Edge.mk' (SSet.yonedaEquiv a)
  let h : SSet.Edge (Z.δ 1 (SSet.yonedaEquiv a)) (Z.δ 0 (SSet.yonedaEquiv b)) :=
    SSet.Edge.mk (SSet.yonedaEquiv b) w₀.symm rfl
  obtain ⟨g, ⟨t⟩, _⟩ := complete_triangle_left hX (e.map f) (h.map f)
    (hZ (SSet.yonedaEquiv a)) (hZ (SSet.yonedaEquiv b))
  let σ : (Δ[2] : SSet.{u}) ⟶ X := SSet.yonedaEquiv.symm t.simplex
  have h₀₁ : SSet.stdSimplex.δ 2 ≫ σ = a ≫ f := by
    apply SSet.yonedaEquiv.injective
    rw [yonedaEquiv_coface, SSet.yonedaEquiv_comp]
    change X.δ 2 (SSet.yonedaEquiv (SSet.yonedaEquiv.symm t.simplex)) = (e.map f).edge
    rw [Equiv.apply_symm_apply]
    exact t.d₂
  have h₀₂ : SSet.stdSimplex.δ 1 ≫ σ = b ≫ f := by
    apply SSet.yonedaEquiv.injective
    rw [yonedaEquiv_coface, SSet.yonedaEquiv_comp]
    change X.δ 1 (SSet.yonedaEquiv (SSet.yonedaEquiv.symm t.simplex)) = (h.map f).edge
    rw [Equiv.apply_symm_apply]
    exact t.d₁
  refine ⟨σ, ?_⟩
  apply SSet.horn₂₀.isPushout.hom_ext
  · rw [← Category.assoc, ← Category.assoc, horn₀_inl_comp]
    exact h₀₁.symm
  · rw [← Category.assoc, ← Category.assoc, horn₀_inr_comp]
    exact h₀₂.symm

/-- Fill an actual right outer two-horn after mapping all its edges to original invertible edges. -/
theorem outer22_filling {X Z : SSet.{u}} (hX : innerHornFillers X) (f : Z ⟶ X)
    (hZ : ∀ e : Z.obj (op ⦋1⦌), edgeIsInvertible X (f.app (op ⦋1⦌) e))
    (σ₀ : (Λ[2, 2] : SSet.{u}) ⟶ Z) :
    ∃ σ : (Δ[2] : SSet.{u}) ⟶ X, σ₀ ≫ f = Λ[2, 2].ι ≫ σ := by
  let a : (Δ[1] : SSet.{u}) ⟶ Z := SSet.horn₂₂.ι₀₂ ≫ σ₀
  let b : (Δ[1] : SSet.{u}) ⟶ Z := SSet.horn₂₂.ι₁₂ ≫ σ₀
  have w : SSet.stdSimplex.δ 0 ≫ a = SSet.stdSimplex.δ 0 ≫ b := by
    change SSet.stdSimplex.δ 0 ≫ (SSet.horn₂₂.ι₀₂ ≫ σ₀) =
      SSet.stdSimplex.δ 0 ≫ (SSet.horn₂₂.ι₁₂ ≫ σ₀)
    rw [← Category.assoc, ← Category.assoc, SSet.horn₂₂.isPushout.w]
  have w₀ : Z.δ 0 (SSet.yonedaEquiv a) = Z.δ 0 (SSet.yonedaEquiv b) := by
    simpa only [yonedaEquiv_coface] using congrArg SSet.yonedaEquiv w
  let h : SSet.Edge (Z.δ 1 (SSet.yonedaEquiv a)) (Z.δ 0 (SSet.yonedaEquiv a)) :=
    SSet.Edge.mk' (SSet.yonedaEquiv a)
  let g : SSet.Edge (Z.δ 1 (SSet.yonedaEquiv b)) (Z.δ 0 (SSet.yonedaEquiv a)) :=
    SSet.Edge.mk (SSet.yonedaEquiv b) rfl w₀.symm
  obtain ⟨e, ⟨t⟩, _⟩ := complete_triangle_right hX (g.map f) (h.map f)
    (hZ (SSet.yonedaEquiv b)) (hZ (SSet.yonedaEquiv a))
  let σ : (Δ[2] : SSet.{u}) ⟶ X := SSet.yonedaEquiv.symm t.simplex
  have h₀₂ : SSet.stdSimplex.δ 1 ≫ σ = a ≫ f := by
    apply SSet.yonedaEquiv.injective
    rw [yonedaEquiv_coface, SSet.yonedaEquiv_comp]
    change X.δ 1 (SSet.yonedaEquiv (SSet.yonedaEquiv.symm t.simplex)) = (h.map f).edge
    rw [Equiv.apply_symm_apply]
    exact t.d₁
  have h₁₂ : SSet.stdSimplex.δ 0 ≫ σ = b ≫ f := by
    apply SSet.yonedaEquiv.injective
    rw [yonedaEquiv_coface, SSet.yonedaEquiv_comp]
    change X.δ 0 (SSet.yonedaEquiv (SSet.yonedaEquiv.symm t.simplex)) = (g.map f).edge
    rw [Equiv.apply_symm_apply]
    exact t.d₀
  refine ⟨σ, ?_⟩
  apply SSet.horn₂₂.isPushout.hom_ext
  · rw [← Category.assoc, ← Category.assoc, horn₂_inl_comp]
    exact h₀₂.symm
  · rw [← Category.assoc, ← Category.assoc, horn₂_inr_comp]
    exact h₁₂.symm

end

end DaggerOriginalQuasicategoryOuterTwoHorns
