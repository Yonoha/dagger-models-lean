import NativeStdSimplexMidpoint

/-! Native convex line segments in the standard simplex, with affine pushforward and continuity. -/
set_option autoImplicit false
universe u v
namespace DaggerNativeStdSimplexInterpolation
noncomputable section
variable {I : Type u} {J : Type v} [Fintype I] [Fintype J]

def blend (x y : stdSimplex ℝ I) (t : unitInterval) : stdSimplex ℝ I :=
  ⟨AffineMap.lineMap (x : I → ℝ) (y : I → ℝ) (t : ℝ),
    (convex_stdSimplex ℝ I).lineMap_mem x.property y.property t.property⟩

theorem blend_coe (x y : stdSimplex ℝ I) (t : unitInterval) :
    (blend x y t : I → ℝ) = (1 - (t : ℝ)) • (x : I → ℝ) + (t : ℝ) • (y : I → ℝ) :=
  AffineMap.lineMap_apply_module _ _ _

theorem blend_zero (x y : stdSimplex ℝ I) : blend x y 0 = x := by
  apply stdSimplex.ext
  exact AffineMap.lineMap_apply_zero _ _

theorem blend_one (x y : stdSimplex ℝ I) : blend x y 1 = y := by
  apply stdSimplex.ext
  exact AffineMap.lineMap_apply_one _ _

theorem map_blend (f : I → J) (x y : stdSimplex ℝ I) (t : unitInterval) :
    stdSimplex.map f (blend x y t) = blend (stdSimplex.map f x) (stdSimplex.map f y) t := by
  apply stdSimplex.ext
  change (FunOnFinite.linearMap ℝ ℝ f)
      (AffineMap.lineMap (x : I → ℝ) (y : I → ℝ) (t : ℝ)) =
    AffineMap.lineMap ((FunOnFinite.linearMap ℝ ℝ f) x)
      ((FunOnFinite.linearMap ℝ ℝ f) y) (t : ℝ)
  simp only [AffineMap.lineMap_apply_module, map_add, map_smul]

theorem continuous_blend :
    Continuous (fun p : stdSimplex ℝ I × stdSimplex ℝ I × unitInterval ↦
      blend p.1 p.2.1 p.2.2) := by
  have hx : Continuous (fun p : stdSimplex ℝ I × stdSimplex ℝ I × unitInterval ↦
      (p.1 : I → ℝ)) := continuous_subtype_val.comp continuous_fst
  have hy : Continuous (fun p : stdSimplex ℝ I × stdSimplex ℝ I × unitInterval ↦
      (p.2.1 : I → ℝ)) := continuous_subtype_val.comp (continuous_fst.comp continuous_snd)
  have ht : Continuous (fun p : stdSimplex ℝ I × stdSimplex ℝ I × unitInterval ↦
      (p.2.2 : ℝ)) := continuous_subtype_val.comp (continuous_snd.comp continuous_snd)
  unfold blend
  apply Continuous.subtype_mk
  simp only [AffineMap.lineMap_apply_module]
  exact ((continuous_const.sub ht).smul hx).add (ht.smul hy)

end
end DaggerNativeStdSimplexInterpolation
