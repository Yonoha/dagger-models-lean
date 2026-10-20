import OriginalOrdinaryCoreHornFillerMembership

/-!
# Composition of actual edges from the literal inner-horn condition

Mathlib's pushout describing the original (2,1)-horn assembles two consecutive
edges with their actual shared endpoint. Filling that horn produces an actual
CompStruct in the input, in arbitrary universe. No alternative homotopy category
or extra triangle-filling assumption is introduced.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open DaggerOriginalInnerHornFillers
open DaggerOriginalOrdinaryKanCoreKanInverseEdges

universe u

namespace DaggerOriginalQuasicategoryComposeEdges

noncomputable section

/-- The first inner-horn leg followed by inclusion is exactly the original [0,1] coface. -/
theorem horn₁_inl_comp :
    SSet.horn₂₁.ι₀₁.{u} ≫ (Λ[2, 1] : (Δ[2] : SSet.{u}).Subcomplex).ι =
      SSet.stdSimplex.δ 2 := by
  simp [SSet.horn₂₁.ι₀₁]

/-- The second inner-horn leg followed by inclusion is exactly the original [1,2] coface. -/
theorem horn₁_inr_comp :
    SSet.horn₂₁.ι₁₂.{u} ≫ (Λ[2, 1] : (Δ[2] : SSet.{u}).Subcomplex).ι =
      SSet.stdSimplex.δ 0 := by
  simp [SSet.horn₂₁.ι₁₂]

/-- Two consecutive original edges admit an actual composition triangle in the same input. -/
theorem compose_edges {X : SSet.{u}} (hX : innerHornFillers X)
    {x y z : X.obj (op ⦋0⦌)} (e : SSet.Edge x y) (g : SSet.Edge y z) :
    ∃ h : SSet.Edge x z, Nonempty (e.CompStruct g h) := by
  let a : (Δ[1] : SSet.{u}) ⟶ X := SSet.yonedaEquiv.symm e.edge
  let b : (Δ[1] : SSet.{u}) ⟶ X := SSet.yonedaEquiv.symm g.edge
  have w : SSet.stdSimplex.δ 0 ≫ a = SSet.stdSimplex.δ 1 ≫ b := by
    apply SSet.yonedaEquiv.injective
    rw [yonedaEquiv_coface, yonedaEquiv_coface]
    simp only [a, b, Equiv.apply_symm_apply, e.tgt_eq, g.src_eq]
  let φ := SSet.horn₂₁.isPushout.desc a b w
  obtain ⟨μ, hμ⟩ := hX (by decide) (by decide) φ
  have h01 : SSet.stdSimplex.δ 2 ≫ μ = a := by
    rw [← horn₁_inl_comp, Category.assoc, ← hμ]
    exact SSet.horn₂₁.isPushout.inl_desc a b w
  have h12 : SSet.stdSimplex.δ 0 ≫ μ = b := by
    rw [← horn₁_inr_comp, Category.assoc, ← hμ]
    exact SSet.horn₂₁.isPushout.inr_desc a b w
  have d2 : X.δ 2 (SSet.yonedaEquiv μ) = e.edge := by
    simpa only [yonedaEquiv_coface, a, Equiv.apply_symm_apply] using
      congrArg SSet.yonedaEquiv h01
  have d0 : X.δ 0 (SSet.yonedaEquiv μ) = g.edge := by
    simpa only [yonedaEquiv_coface, b, Equiv.apply_symm_apply] using
      congrArg SSet.yonedaEquiv h12
  obtain ⟨a0, a1, a2, e01, e12, e02, t, ht⟩ :=
    SSet.Edge.CompStruct.exists_of_simplex (SSet.yonedaEquiv μ)
  have he01 : e01.edge = e.edge := by
    rw [← t.d₂, ht]
    exact d2
  have he12 : e12.edge = g.edge := by
    rw [← t.d₀, ht]
    exact d0
  have ha0 : a0 = x := by rw [← e01.src_eq, he01, e.src_eq]
  have ha1 : a1 = y := by rw [← e01.tgt_eq, he01, e.tgt_eq]
  have ha2 : a2 = z := by rw [← e12.tgt_eq, he12, g.tgt_eq]
  subst a0 a1 a2
  have h01e : e01 = e := SSet.Edge.ext he01
  have h12e : e12 = g := SSet.Edge.ext he12
  subst e01 e12
  exact ⟨e02, ⟨t⟩⟩

end

end DaggerOriginalQuasicategoryComposeEdges
