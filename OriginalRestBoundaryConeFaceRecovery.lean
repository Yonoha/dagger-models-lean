import OriginalRestBoundaryConeFaceOperators

/-!
# Original cone transposition recovers every actual remaining standard coface

Original Yoneda evaluates the native cone unit at the same original simplex
operator. The verified exact chart-operator equation therefore identifies each
transposed unit face with the actual original remaining boundary coface. Target
naturality retains the same face equality for every original map into X.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerOriginalOrdinalJoinLeft DaggerOriginalSimplexCoslice
open DaggerOriginalJoinedHornGeometry DaggerOriginalPrefixBoundarySuccessorShapes
open DaggerOriginalPrefixBoundaryConeOperators DaggerOriginalPrefixBoundaryConeUnit
open DaggerOriginalZeroJoinYonedaCorrespondence DaggerOriginalZeroJoinStandardCofaces
open DaggerOriginalZeroJoinStandardTransposition
open DaggerOriginalPrefixBoundaryConeTransposition
open DaggerOriginalRestBoundaryInverseFaceMaps DaggerOriginalRestBoundaryInverseGluing
open DaggerOriginalRestBoundaryConeFaceOperators

universe u

namespace DaggerOriginalRestBoundaryConeFaceRecovery

noncomputable section

/-- The native cone unit evaluates to the actual original prepended simplex operator. -/
theorem zeroJoinYoneda_cone_unit_ambient (k n : ℕ) (d : SimplexCategory)
    (a : SSet.stdSimplex.obj d ⟶ (prefixBoundary k n : SSet.{u})) :
    zeroJoinYonedaEquiv d (restPrefixBoundary k n) (a ≫ prefixConeBoundaryUnit k n) ≫
        (restPrefixBoundary k n).ι =
      SSet.stdSimplex.map (prefixConeOperator k n
        (SSet.stdSimplex.objEquiv (SSet.yonedaEquiv (a ≫ (prefixBoundary k n).ι)))) := by
  apply (SSet.yonedaEquiv (X := (Δ[k + 1 + n + 1] : SSet.{u}))
    (n := (ordinalJoinLeft ⦋0⦌).obj d)).injective
  rw [SSet.yonedaEquiv_comp, zeroJoinYonedaEquiv_eval, SSet.yonedaEquiv_comp,
    SSet.stdSimplex.yonedaEquiv_map, SSet.yonedaEquiv_comp]
  rfl

/-- Each original prefix face of the cone unit retains that same actual original coface. -/
theorem zeroJoinYoneda_cone_unit_prefix_face (k n : ℕ) (j : Fin (k + 1)) :
    zeroJoinYonedaEquiv ⦋k + n⦌ (restPrefixBoundary k n)
        (prefixFaceBoundaryInclusion.{u} k n j ≫ prefixConeBoundaryUnit k n) ≫
        (restPrefixBoundary k n).ι =
      SSet.stdSimplex.map (prefixConeOperator k n (SimplexCategory.δ (prefixIndex k n j))) := by
  have h := zeroJoinYoneda_cone_unit_ambient k n ⦋k + n⦌ (prefixFaceBoundaryInclusion k n j)
  have ho : SSet.stdSimplex.objEquiv.{u}
      (SSet.yonedaEquiv (prefixFaceBoundaryInclusion.{u} k n j ≫ (prefixBoundary k n).ι)) =
    SimplexCategory.δ (prefixIndex k n j) := by
    rw [prefixFaceBoundaryInclusion_comp]
    change SSet.stdSimplex.objEquiv.{u}
      (SSet.yonedaEquiv (SSet.stdSimplex.{u}.map (SimplexCategory.δ (prefixIndex k n j)))) = _
    rw [SSet.stdSimplex.yonedaEquiv_map, Equiv.apply_symm_apply]
  rw [ho] at h
  exact h

/-- Standard transposition of the original cone unit recovers the actual remaining coface. -/
theorem inverseRestFaceStandardMap_cone_unit (k n : ℕ) (j : Fin (k + 1)) :
    inverseRestFaceStandardMap.{u} k n j (prefixConeBoundaryUnit k n) =
      restFaceBoundaryInclusion k n j := by
  apply (cancel_mono (restPrefixBoundary k n).ι).mp
  rw [restFaceBoundaryInclusion_comp]
  dsimp only [inverseRestFaceStandardMap, zeroJoinStandardTranspose]
  simp only [Category.assoc]
  rw [zeroJoinYoneda_cone_unit_prefix_face]
  rw [← Functor.map_comp, ← Functor.map_comp, restConeFaceOperator_eq_coface]
  rfl

/-- Each actual inverse-construction standard face commutes with every original target map. -/
theorem inverseRestFaceStandardMap_postcomp {X Y : SSet.{u}} (k n : ℕ) (j : Fin (k + 1))
    (t : (prefixBoundary k n : SSet.{u}) ⟶ joinedPresheaf ⦋0⦌ X) (p : X ⟶ Y) :
    inverseRestFaceStandardMap k n j
        (t ≫ Functor.whiskerLeft (ordinalJoinLeft ⦋0⦌).op p) =
      inverseRestFaceStandardMap k n j t ≫ p := by
  dsimp only [inverseRestFaceStandardMap]
  rw [← Category.assoc, zeroJoinStandardTranspose_postcomp, Category.assoc]

/-- For every actual remaining-boundary map, transposition recovers each original coface map. -/
theorem inverseRestFaceStandardMap_transpose {X : SSet.{u}} (k n : ℕ) (j : Fin (k + 1))
    (g : (restPrefixBoundary k n : SSet.{u}) ⟶ X) :
    inverseRestFaceStandardMap k n j (prefixConeTranspose k n g) =
      restFaceBoundaryInclusion k n j ≫ g := by
  rw [prefixConeTranspose, inverseRestFaceStandardMap_postcomp,
    inverseRestFaceStandardMap_cone_unit]

end

end DaggerOriginalRestBoundaryConeFaceRecovery
