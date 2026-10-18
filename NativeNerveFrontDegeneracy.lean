import NativeNerveFrontSubdivision
import Mathlib.AlgebraicTopology.SimplicialSet.Degenerate

/-! Native degeneracies commute with adjoining the first original arrow. -/
set_option autoImplicit false
open CategoryTheory Simplicial
universe u v
namespace DaggerNativeNerveFrontDegeneracy

variable {C : Type u} [Category.{v} C]

theorem sigma_left {n : ℕ} (c : ComposableArrows C n) (i : Fin (n + 1)) :
    ((nerve C).σ i c).left = c.left := by
  change c.obj (i.predAbove 0) = c.obj 0
  rw [Fin.predAbove_right_zero]

theorem sigma_zero {n : ℕ} (c : ComposableArrows C n) :
    (nerve C).σ (0 : Fin (n + 1)) c = c.precomp (𝟙 c.left) := by
  refine ComposableArrows.ext_succ rfl ?_ ?_
  · simpa only [nerve.δ₀_eq, ComposableArrows.precomp_δ₀] using
      SSet.δ_comp_σ_self_apply (S := nerve C) (0 : Fin (n + 1)) c
  · simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    change c.map (𝟙 (0 : Fin (n + 1))) = 𝟙 c.left
    exact c.map_id _

theorem sigma_succ_precomp {n : ℕ} (c : ComposableArrows C n) {X : C}
    (f : X ⟶ c.left) (i : Fin (n + 1)) :
    (nerve C).σ i.succ (c.precomp f) =
      ((nerve C).σ i c).precomp (f ≫ eqToHom (sigma_left c i).symm) := by
  refine ComposableArrows.ext_succ ?_ ?_ ?_
  · change (c.precomp f).obj (i.succ.predAbove 0) = X
    rw [Fin.predAbove_right_zero]
    rfl
  · have h := SSet.δ_comp_σ_of_le_apply (S := nerve C)
      (i := (0 : Fin (n + 2))) (j := i) (Fin.zero_le _) (c.precomp f)
    simpa only [Fin.castSucc_zero, nerve.δ₀_eq, ComposableArrows.precomp_δ₀] using h
  · simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    change ComposableArrows.Precomp.map c f (i.succ.predAbove 0)
      (i.succ.predAbove (0 : Fin (n + 2)).succ) (by simp) = _
    simp [Fin.predAbove, Fin.lt_def, ComposableArrows.Precomp.map]
    rfl

end DaggerNativeNerveFrontDegeneracy
