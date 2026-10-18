import OriginalQuasicategoryInverseEdgeRepresentatives

/-!
# Actual inner tetrahedron fillers with fixed original triangle faces

Reuse Mathlib's colimit descriptions of the literal (3,1)- and (3,2)-horns.
The input's literal inner-horn filling condition gives the missing composition
triangle in the original simplicial set, with exactly the supplied edges.
These are the three-dimensional mechanisms used in the pinned Mathlib theory
of two-truncated quasicategories, proved here in arbitrary universe.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerOriginalInnerHornFillers
open DaggerOriginalOrdinaryKanCoreKanInverseEdges

universe u

namespace DaggerOriginalQuasicategoryTetrahedronFillers

noncomputable section

/-- An actual (3,1)-inner horn gives the fourth original composition triangle. -/
theorem fill31 {X : SSet.{u}} (hX : innerHornFillers X)
    {x₀ x₁ x₂ x₃ : X.obj (op ⦋0⦌)}
    {e₀₁ : SSet.Edge x₀ x₁} {e₁₂ : SSet.Edge x₁ x₂} {e₂₃ : SSet.Edge x₂ x₃}
    {e₀₂ : SSet.Edge x₀ x₂} {e₁₃ : SSet.Edge x₁ x₃} {e₀₃ : SSet.Edge x₀ x₃}
    (t₃ : e₀₁.CompStruct e₁₂ e₀₂) (t₀ : e₁₂.CompStruct e₂₃ e₁₃)
    (t₂ : e₀₁.CompStruct e₁₃ e₀₃) : Nonempty (e₀₂.CompStruct e₂₃ e₀₃) := by
  let f₀ : (Δ[2] : SSet.{u}) ⟶ X := SSet.yonedaEquiv.symm t₀.simplex
  let f₂ : (Δ[2] : SSet.{u}) ⟶ X := SSet.yonedaEquiv.symm t₂.simplex
  let f₃ : (Δ[2] : SSet.{u}) ⟶ X := SSet.yonedaEquiv.symm t₃.simplex
  have w₁₂ : SSet.stdSimplex.δ 2 ≫ f₀ = SSet.stdSimplex.δ 0 ≫ f₃ := by
    apply SSet.yonedaEquiv.injective
    rw [yonedaEquiv_coface, yonedaEquiv_coface]
    simp only [f₀, f₃, Equiv.apply_symm_apply, t₀.d₂, t₃.d₀]
  have w₁₃ : SSet.stdSimplex.δ 1 ≫ f₀ = SSet.stdSimplex.δ 0 ≫ f₂ := by
    apply SSet.yonedaEquiv.injective
    rw [yonedaEquiv_coface, yonedaEquiv_coface]
    simp only [f₀, f₂, Equiv.apply_symm_apply, t₀.d₁, t₂.d₀]
  have w₂₃ : SSet.stdSimplex.δ 2 ≫ f₂ = SSet.stdSimplex.δ 2 ≫ f₃ := by
    apply SSet.yonedaEquiv.injective
    rw [yonedaEquiv_coface, yonedaEquiv_coface]
    simp only [f₂, f₃, Equiv.apply_symm_apply, t₂.d₂, t₃.d₂]
  let φ := SSet.horn₃₁.desc f₀ f₂ f₃ w₁₂ w₁₃ w₂₃
  obtain ⟨μ, hμ⟩ := hX (by decide) (by decide) φ
  have h₀ : SSet.stdSimplex.δ 0 ≫ μ = f₀ := by
    rw [← SSet.horn.ι_ι (1 : Fin 4) 0 (by decide), Category.assoc, ← hμ]
    exact SSet.horn₃₁.ι₀_desc f₀ f₂ f₃ w₁₂ w₁₃ w₂₃
  have h₂ : SSet.stdSimplex.δ 2 ≫ μ = f₂ := by
    rw [← SSet.horn.ι_ι (1 : Fin 4) 2 (by decide), Category.assoc, ← hμ]
    exact SSet.horn₃₁.ι₂_desc f₀ f₂ f₃ w₁₂ w₁₃ w₂₃
  have h₃ : SSet.stdSimplex.δ 3 ≫ μ = f₃ := by
    rw [← SSet.horn.ι_ι (1 : Fin 4) 3 (by decide), Category.assoc, ← hμ]
    exact SSet.horn₃₁.ι₃_desc f₀ f₂ f₃ w₁₂ w₁₃ w₂₃
  let s := SSet.yonedaEquiv μ
  have d₀ : X.δ 0 s = t₀.simplex := by
    simpa only [yonedaEquiv_coface, f₀, Equiv.apply_symm_apply] using
      congrArg SSet.yonedaEquiv h₀
  have d₂ : X.δ 2 s = t₂.simplex := by
    simpa only [yonedaEquiv_coface, f₂, Equiv.apply_symm_apply] using
      congrArg SSet.yonedaEquiv h₂
  have d₃ : X.δ 3 s = t₃.simplex := by
    simpa only [yonedaEquiv_coface, f₃, Equiv.apply_symm_apply] using
      congrArg SSet.yonedaEquiv h₃
  refine ⟨SSet.Edge.CompStruct.mk (X.δ 1 s) ?_ ?_ ?_⟩
  · calc
      X.δ 2 (X.δ 1 s) = X.δ 1 (X.δ 3 s) :=
        (congrFun (X.δ_comp_δ (i := 1) (j := 2) (by decide)) s).symm
      _ = e₀₂.edge := by rw [d₃, t₃.d₁]
  · calc
      X.δ 0 (X.δ 1 s) = X.δ 0 (X.δ 0 s) :=
        congrFun (X.δ_comp_δ (i := 0) (j := 0) (by decide)) s
      _ = e₂₃.edge := by rw [d₀, t₀.d₀]
  · calc
      X.δ 1 (X.δ 1 s) = X.δ 1 (X.δ 2 s) :=
        (congrFun (X.δ_comp_δ (i := 1) (j := 1) (by decide)) s).symm
      _ = e₀₃.edge := by rw [d₂, t₂.d₁]

/-- An actual (3,2)-inner horn gives the fourth original composition triangle. -/
theorem fill32 {X : SSet.{u}} (hX : innerHornFillers X)
    {x₀ x₁ x₂ x₃ : X.obj (op ⦋0⦌)}
    {e₀₁ : SSet.Edge x₀ x₁} {e₁₂ : SSet.Edge x₁ x₂} {e₂₃ : SSet.Edge x₂ x₃}
    {e₀₂ : SSet.Edge x₀ x₂} {e₁₃ : SSet.Edge x₁ x₃} {e₀₃ : SSet.Edge x₀ x₃}
    (t₃ : e₀₁.CompStruct e₁₂ e₀₂) (t₀ : e₁₂.CompStruct e₂₃ e₁₃)
    (t₁ : e₀₂.CompStruct e₂₃ e₀₃) : Nonempty (e₀₁.CompStruct e₁₃ e₀₃) := by
  let f₀ : (Δ[2] : SSet.{u}) ⟶ X := SSet.yonedaEquiv.symm t₀.simplex
  let f₁ : (Δ[2] : SSet.{u}) ⟶ X := SSet.yonedaEquiv.symm t₁.simplex
  let f₃ : (Δ[2] : SSet.{u}) ⟶ X := SSet.yonedaEquiv.symm t₃.simplex
  have w₀₂ : SSet.stdSimplex.δ 2 ≫ f₁ = SSet.stdSimplex.δ 1 ≫ f₃ := by
    apply SSet.yonedaEquiv.injective
    rw [yonedaEquiv_coface, yonedaEquiv_coface]
    simp only [f₁, f₃, Equiv.apply_symm_apply, t₁.d₂, t₃.d₁]
  have w₁₂ : SSet.stdSimplex.δ 2 ≫ f₀ = SSet.stdSimplex.δ 0 ≫ f₃ := by
    apply SSet.yonedaEquiv.injective
    rw [yonedaEquiv_coface, yonedaEquiv_coface]
    simp only [f₀, f₃, Equiv.apply_symm_apply, t₀.d₂, t₃.d₀]
  have w₂₃ : SSet.stdSimplex.δ 0 ≫ f₀ = SSet.stdSimplex.δ 0 ≫ f₁ := by
    apply SSet.yonedaEquiv.injective
    rw [yonedaEquiv_coface, yonedaEquiv_coface]
    simp only [f₀, f₁, Equiv.apply_symm_apply, t₀.d₀, t₁.d₀]
  let φ := SSet.horn₃₂.desc f₀ f₁ f₃ w₀₂ w₁₂ w₂₃
  obtain ⟨μ, hμ⟩ := hX (by decide) (by decide) φ
  have h₀ : SSet.stdSimplex.δ 0 ≫ μ = f₀ := by
    rw [← SSet.horn.ι_ι (2 : Fin 4) 0 (by decide), Category.assoc, ← hμ]
    exact SSet.horn₃₂.ι₀_desc f₀ f₁ f₃ w₀₂ w₁₂ w₂₃
  have h₁ : SSet.stdSimplex.δ 1 ≫ μ = f₁ := by
    rw [← SSet.horn.ι_ι (2 : Fin 4) 1 (by decide), Category.assoc, ← hμ]
    exact SSet.horn₃₂.ι₁_desc f₀ f₁ f₃ w₀₂ w₁₂ w₂₃
  have h₃ : SSet.stdSimplex.δ 3 ≫ μ = f₃ := by
    rw [← SSet.horn.ι_ι (2 : Fin 4) 3 (by decide), Category.assoc, ← hμ]
    exact SSet.horn₃₂.ι₃_desc f₀ f₁ f₃ w₀₂ w₁₂ w₂₃
  let s := SSet.yonedaEquiv μ
  have d₀ : X.δ 0 s = t₀.simplex := by
    simpa only [yonedaEquiv_coface, f₀, Equiv.apply_symm_apply] using
      congrArg SSet.yonedaEquiv h₀
  have d₁ : X.δ 1 s = t₁.simplex := by
    simpa only [yonedaEquiv_coface, f₁, Equiv.apply_symm_apply] using
      congrArg SSet.yonedaEquiv h₁
  have d₃ : X.δ 3 s = t₃.simplex := by
    simpa only [yonedaEquiv_coface, f₃, Equiv.apply_symm_apply] using
      congrArg SSet.yonedaEquiv h₃
  refine ⟨SSet.Edge.CompStruct.mk (X.δ 2 s) ?_ ?_ ?_⟩
  · calc
      X.δ 2 (X.δ 2 s) = X.δ 2 (X.δ 3 s) :=
        (congrFun (X.δ_comp_δ (i := 2) (j := 2) (by decide)) s).symm
      _ = e₀₁.edge := by rw [d₃, t₃.d₂]
  · calc
      X.δ 0 (X.δ 2 s) = X.δ 1 (X.δ 0 s) :=
        congrFun (X.δ_comp_δ (i := 0) (j := 1) (by decide)) s
      _ = e₁₃.edge := by rw [d₀, t₀.d₁]
  · calc
      X.δ 1 (X.δ 2 s) = X.δ 1 (X.δ 1 s) :=
        congrFun (X.δ_comp_δ (i := 1) (j := 1) (by decide)) s
      _ = e₀₃.edge := by rw [d₁, t₁.d₁]

end

end DaggerOriginalQuasicategoryTetrahedronFillers
