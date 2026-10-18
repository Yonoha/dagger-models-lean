import NativeReducedPathEdgeExtension
import Mathlib.Combinatorics.Quiver.Covering

/-! Each nonidentity native free-groupoid normal path has a unique descending signed edge. -/
set_option autoImplicit false
open CategoryTheory
open DaggerNativeSignedPathWords DaggerNativeFreeGroupoidWordLabels
open DaggerNativeFreeGroupoidNormalPath DaggerNativeSignedPathReduction
open DaggerNativeReducedPathEdgeExtension
universe u
namespace DaggerNativeFreeGroupoidDescendingEdges
noncomputable section

variable (V : Type u) [Quiver.{u + 1} V]

theorem normalPath_of_descending_edge {a b c : Quiver.Symmetrify V}
    (f : (quotientMap V).obj a ⟶ (quotientMap V).obj b) (e : b ⟶ c)
    (hd : norm V (f ≫ (quotientMap V).map e.toPath) + 1 = norm V f) :
    normalPath V f = (normalPath V (f ≫ (quotientMap V).map e.toPath)).cons
      (Quiver.reverse e) := by
  let p := normalPath V f
  have he : (quotientMap V).map (p.cons e) = f ≫ (quotientMap V).map e.toPath := by
    change (quotientMap V).map (p ≫ e.toPath) = _
    rw [CategoryTheory.Functor.map_comp, quotient_normalPath]
  rcases reduced_extension_or_cancel V p (normalPath_reduced V f) e with hr | ⟨q, hq, hr⟩
  · have hn := norm_of_reduced V (p.cons e) hr
    rw [he] at hn
    change norm V (f ≫ (quotientMap V).map e.toPath) = norm V f + 1 at hn
    omega
  · have hg : f ≫ (quotientMap V).map e.toPath = (quotientMap V).map q := by
      rw [← he, hq]
      exact quotient_backtrack V q e
    rw [hg, normalPath_of_reduced V q hr]
    exact hq

theorem existsUnique_descending_edge {a b : Quiver.Symmetrify V}
    (f : (quotientMap V).obj a ⟶ (quotientMap V).obj b) (hf : norm V f ≠ 0) :
    ∃! s : Quiver.Star b,
      norm V (f ≫ (quotientMap V).map s.2.toPath) + 1 = norm V f := by
  let p := normalPath V f
  have hp : p.length ≠ 0 := hf
  obtain ⟨c, q, e, he⟩ := (Quiver.Path.length_ne_zero_iff_eq_cons p).mp hp
  have hr : FreeGroup.IsReduced (word q) := by
    have hr := normalPath_reduced V f
    change FreeGroup.IsReduced (word p) at hr
    rw [he] at hr
    exact hr.tail
  have hg : f ≫ (quotientMap V).map (Quiver.reverse e).toPath = (quotientMap V).map q := by
    have hmap := quotient_normalPath V f
    change (quotientMap V).map p = f at hmap
    rw [← hmap, he]
    change (quotientMap V).map (q.cons e) ≫
      (quotientMap V).map (Quiver.reverse e).toPath = _
    rw [← CategoryTheory.Functor.map_comp]
    simpa only [Quiver.reverse_reverse] using
      quotient_backtrack V q (Quiver.reverse e)
  refine ⟨⟨c, Quiver.reverse e⟩, ?_, ?_⟩
  · change norm V (f ≫ (quotientMap V).map (Quiver.reverse e).toPath) + 1 = norm V f
    rw [hg, norm_of_reduced V q hr]
    change q.length + 1 = p.length
    rw [he]
    rfl
  · rintro ⟨c', e'⟩ hs
    have hh := normalPath_of_descending_edge V f e' hs
    change p = _ at hh
    rw [he] at hh
    have hc := Quiver.Path.obj_eq_of_cons_eq_cons hh
    subst c'
    have he' : e = Quiver.reverse e' := eq_of_heq (Quiver.Path.hom_heq_of_cons_eq_cons hh)
    have hei : e' = Quiver.reverse e := by
      rw [he', Quiver.reverse_reverse]
    exact Sigma.ext rfl (heq_of_eq hei)

end
end DaggerNativeFreeGroupoidDescendingEdges
