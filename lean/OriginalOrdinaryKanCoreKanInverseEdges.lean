import OriginalOrdinaryKanCoreEdgeMaximality
import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex
import Mathlib.AlgebraicTopology.SimplicialSet.CompStruct
import Mathlib.AlgebraicTopology.SimplicialSet.HornColimits

/-!
# Actual outer 2-horn inverse edges in a Kan complex

Use the retained Kan horn filling property and the native outer-horn pushouts.
All edges and endpoint equalities remain in the original simplicial set.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

universe u

namespace DaggerOriginalOrdinaryKanCoreKanInverseEdges

noncomputable section

/-- The original Yoneda equivalence identifies precomposition with a literal face map. -/
theorem yonedaEquiv_coface (X : SSet.{u}) {n : ℕ} (i : Fin (n + 2))
    (μ : (Δ[n + 1] : SSet.{u}) ⟶ X) :
    SSet.yonedaEquiv (SSet.stdSimplex.δ i ≫ μ) =
      X.δ i (SSet.yonedaEquiv μ) :=
  (uliftYonedaEquiv_naturality (F := X) μ (SimplexCategory.δ i).op).symm

/-- The first face leg is exactly the original [0,1] coface after inclusion. -/
theorem horn₀_inl_comp :
    SSet.horn₂₀.ι₀₁.{u} ≫ (Λ[2, 0] : (Δ[2] : SSet.{u}).Subcomplex).ι =
      SSet.stdSimplex.δ 2 := by
  simp [SSet.horn₂₀.ι₀₁]

/-- The second face leg is exactly the original [0,2] coface after inclusion. -/
theorem horn₀_inr_comp :
    SSet.horn₂₀.ι₀₂.{u} ≫ (Λ[2, 0] : (Δ[2] : SSet.{u}).Subcomplex).ι =
      SSet.stdSimplex.δ 1 := by
  simp [SSet.horn₂₀.ι₀₂]

/-- Filling the actual outer 2-horn produces a right inverse triangle with both fixed endpoints. -/
theorem kan_right_inverse_edge {X : SSet.{u}} [X.KanComplex]
    {x y : X.obj (op ⦋0⦌)} (e : SSet.Edge x y) :
    ∃ r : SSet.Edge y x, Nonempty (e.CompStruct r (SSet.Edge.id x)) := by
  let a : (Δ[1] : SSet.{u}) ⟶ X := SSet.yonedaEquiv.symm e.edge
  let b : (Δ[1] : SSet.{u}) ⟶ X := SSet.yonedaEquiv.symm (SSet.Edge.id x).edge
  have w : SSet.stdSimplex.δ 1 ≫ a = SSet.stdSimplex.δ 1 ≫ b := by
    apply SSet.yonedaEquiv.injective
    rw [yonedaEquiv_coface, yonedaEquiv_coface]
    simp only [a, b, Equiv.apply_symm_apply, e.src_eq, SSet.Edge.src_eq]
  let h := SSet.horn₂₀.isPushout.desc a b w
  obtain ⟨μ, hμ⟩ := SSet.KanComplex.hornFilling h
  have h01 : SSet.stdSimplex.δ 2 ≫ μ = a := by
    rw [← horn₀_inl_comp, Category.assoc, ← hμ]
    exact SSet.horn₂₀.isPushout.inl_desc a b w
  have h02 : SSet.stdSimplex.δ 1 ≫ μ = b := by
    rw [← horn₀_inr_comp, Category.assoc, ← hμ]
    exact SSet.horn₂₀.isPushout.inr_desc a b w
  have d2 : X.δ 2 (SSet.yonedaEquiv μ) = e.edge := by
    simpa only [yonedaEquiv_coface, a, Equiv.apply_symm_apply] using
      congrArg SSet.yonedaEquiv h01
  have d1 : X.δ 1 (SSet.yonedaEquiv μ) = (SSet.Edge.id x).edge := by
    simpa only [yonedaEquiv_coface, b, Equiv.apply_symm_apply] using
      congrArg SSet.yonedaEquiv h02
  obtain ⟨a0, a1, a2, e01, e12, e02, t, ht⟩ :=
    SSet.Edge.CompStruct.exists_of_simplex (SSet.yonedaEquiv μ)
  have he01 : e01.edge = e.edge := by
    rw [← t.d₂, ht]
    exact d2
  have he02 : e02.edge = (SSet.Edge.id x).edge := by
    rw [← t.d₁, ht]
    exact d1
  have ha0 : a0 = x := by rw [← e01.src_eq, he01, e.src_eq]
  have ha1 : a1 = y := by rw [← e01.tgt_eq, he01, e.tgt_eq]
  have ha2 : a2 = x := by rw [← e02.tgt_eq, he02, SSet.Edge.tgt_eq]
  subst a0 a1 a2
  have h01e : e01 = e := SSet.Edge.ext he01
  have h02e : e02 = SSet.Edge.id x := SSet.Edge.ext he02
  subst e01 e02
  exact ⟨e12, ⟨t⟩⟩

end

end DaggerOriginalOrdinaryKanCoreKanInverseEdges
