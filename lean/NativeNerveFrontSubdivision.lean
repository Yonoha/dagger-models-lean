import Mathlib.AlgebraicTopology.SimplicialSet.Nerve

/-! Native first-face identities recover the exact chain after subdividing its first arrow. -/
set_option autoImplicit false
open CategoryTheory Simplicial
universe u v
namespace DaggerNativeNerveFrontSubdivision

variable {C : Type u} [Category.{v} C]

theorem reconstruct {n : ℕ} (c : ComposableArrows C (n + 1)) :
    c.δ₀.precomp (c.map' 0 1) = c :=
  ComposableArrows.ext_succ rfl (by simp) (by simp)

theorem delta_one_precomp_precomp {n : ℕ} (c : ComposableArrows C n)
    {X Y : C} (g : Y ⟶ c.left) (f : X ⟶ Y) :
    (nerve C).δ (1 : Fin (n + 3)) ((c.precomp g).precomp f) = c.precomp (f ≫ g) := by
  refine ComposableArrows.ext_succ rfl ?_ ?_
  · have h := SSet.δ_comp_δ_apply (S := nerve C) (n := n)
      (i := (0 : Fin (n + 2))) (j := 0) (le_refl _) ((c.precomp g).precomp f)
    simpa only [nerve.δ₀_eq, ComposableArrows.precomp_δ₀] using h
  · simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl

end DaggerNativeNerveFrontSubdivision
