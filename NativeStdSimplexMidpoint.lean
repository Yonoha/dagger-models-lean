import Mathlib.AlgebraicTopology.TopologicalSimplex
import Mathlib.LinearAlgebra.AffineSpace.Midpoint
import Mathlib.Tactic.NormNum

/-! Midpoints in the native standard simplex, using Mathlib convexity and affine maps. -/
set_option autoImplicit false
universe u v
namespace DaggerNativeStdSimplexMidpoint
noncomputable section

def realTwoInvertible : Invertible (2 : ℝ) := invertibleOfNonzero (by norm_num)
attribute [local instance] realTwoInvertible

variable {I : Type u} {J : Type v} [Fintype I] [Fintype J]

def halfAverage (x y : stdSimplex ℝ I) : stdSimplex ℝ I :=
  ⟨midpoint ℝ (x : I → ℝ) (y : I → ℝ),
    (convex_stdSimplex ℝ I).midpoint_mem x.property y.property⟩

theorem halfAverage_coe (x y : stdSimplex ℝ I) :
    (halfAverage x y : I → ℝ) = (1 / 2 : ℝ) • ((x : I → ℝ) + (y : I → ℝ)) := by
  simpa only [one_div, invOf_eq_inv] using
    (midpoint_eq_smul_add ℝ (x : I → ℝ) (y : I → ℝ))

theorem halfAverage_comm (x y : stdSimplex ℝ I) : halfAverage x y = halfAverage y x := by
  apply stdSimplex.ext
  exact midpoint_comm (x : I → ℝ) (y : I → ℝ)

theorem halfAverage_self (x : stdSimplex ℝ I) : halfAverage x x = x := by
  apply stdSimplex.ext
  exact midpoint_self ℝ (x : I → ℝ)

theorem map_halfAverage (f : I → J) (x y : stdSimplex ℝ I) :
    stdSimplex.map f (halfAverage x y) = halfAverage (stdSimplex.map f x) (stdSimplex.map f y) := by
  apply stdSimplex.ext
  exact (FunOnFinite.linearMap ℝ ℝ f).toAffineMap.map_midpoint (x : I → ℝ) (y : I → ℝ)

theorem continuous_halfAverage :
    Continuous (fun p : stdSimplex ℝ I × stdSimplex ℝ I ↦ halfAverage p.1 p.2) := by
  unfold halfAverage
  apply Continuous.subtype_mk
  simp_rw [midpoint_eq_smul_add]
  exact continuous_const.smul
    ((continuous_subtype_val.comp continuous_fst).add
      (continuous_subtype_val.comp continuous_snd))

end
end DaggerNativeStdSimplexMidpoint
