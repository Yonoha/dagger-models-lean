import ActualRightConeObjectClassification
import ChosenNecklacePointMaps

/-! Simplices of the literal right cone whose vertices all equal one endpoint lie in that point. -/

set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial
open DaggerOriginalCounitRightCone
open DaggerOriginalCounitRightConeQPushoutSimplexSupport
open DaggerOriginalCounitRightConeQZeroFaceIntersection
open DaggerChosenRigidificationNecklace.NecklaceCode
universe u

namespace DaggerActualRightConePointSupport
noncomputable section

private theorem vertex_naturality {X Y : SSet.{u}} (f : X ⟶ Y) {m : ℕ}
    (x : X.obj (op ⦋m⦌)) (i : Fin (m + 1)) :
    Y.map (SimplexCategory.const ⦋0⦌ ⦋m⦌ i).op (f.app _ x) =
      f.app _ (X.map (SimplexCategory.const ⦋0⦌ ⦋m⦌ i).op x) := by
  exact (congrFun (f.naturality (SimplexCategory.const ⦋0⦌ ⦋m⦌ i).op) x).symm

/-- Any vertex in the attaching face becomes the actual collapsed endpoint. -/
theorem simplexIncl_vertex_preLast (n : ℕ) (i : Fin (n + 2))
    (hi : i ≠ Fin.last (n + 1)) :
    (simplexIncl.{u} n).app (op ⦋0⦌) (SSet.stdSimplex.obj₀Equiv.symm i) = alpha n := by
  have hin : SSet.stdSimplex.obj₀Equiv.symm i ∈ Set.range ((face.{u} n).app (op ⦋0⦌)) := by
    change _ ∈ (SSet.Subcomplex.range
      (SSet.stdSimplex.δ (Fin.last (n + 1)) : (Δ[n] : SSet.{u}) ⟶ Δ[n + 1])).obj _
    rw [SSet.stdSimplex.range_δ, SSet.stdSimplex.mem_face_iff]
    intro j
    have hj : j = 0 := Fin.ext (by omega)
    subst j
    simpa only [SSet.stdSimplex.obj₀Equiv_symm_apply, Finset.mem_compl,
      Finset.mem_singleton] using hi
  obtain ⟨z, hz⟩ := hin
  rw [← hz]
  have h := congrFun (NatTrans.congr_app (face_eq_collapse.{u} n) (op ⦋0⦌)) z
  change (simplexIncl n).app _ ((face n).app _ z) =
    (baseIncl n).app _ ((collapse n).app _ z) at h
  rw [h, zeroSimplex_unique ((collapse n).app _ z)]
  rfl

theorem simplexIncl_vertex_last (n : ℕ) :
    (simplexIncl.{u} n).app (op ⦋0⦌)
      (SSet.stdSimplex.obj₀Equiv.symm (Fin.last (n + 1))) = omega n := rfl

/-- This holds in every degree, without a nondegeneracy or fibrancy assumption. -/
theorem alpha_supported (n m : ℕ) (x : (cone.{u} n).obj (op ⦋m⦌))
    (hx : ∀ i : Fin (m + 1),
      (cone n).map (SimplexCategory.const ⦋0⦌ ⦋m⦌ i).op x = alpha n) :
    x ∈ Set.range ((alphaMap.{u} n).app (op ⦋m⦌)) := by
  rcases cone_simplex_base_or_tip n (op ⦋m⦌) x with hb | ⟨y, hyx, hout⟩
  · exact hb
  · have hin : y ∈ Set.range ((face.{u} n).app (op ⦋m⦌)) := by
      change y ∈ (SSet.Subcomplex.range
        (SSet.stdSimplex.δ (Fin.last (n + 1)) : (Δ[n] : SSet.{u}) ⟶ Δ[n + 1])).obj _
      rw [SSet.stdSimplex.range_δ, SSet.stdSimplex.mem_face_iff]
      intro i
      simp only [Finset.mem_compl, Finset.mem_singleton]
      intro hi
      have h := hx i
      rw [← hyx, vertex_naturality] at h
      change (simplexIncl n).app _ (SSet.stdSimplex.obj₀Equiv.symm (y i)) = alpha n at h
      rw [hi, simplexIncl_vertex_last] at h
      exact alpha_ne_omega n h.symm
    exact False.elim (hout hin)

/-- A simplex entirely at the original tip is the image of that point in the actual pushout. -/
theorem omega_supported (n m : ℕ) (x : (cone.{u} n).obj (op ⦋m⦌))
    (hx : ∀ i : Fin (m + 1),
      (cone n).map (SimplexCategory.const ⦋0⦌ ⦋m⦌ i).op x = omega n) :
    x ∈ Set.range ((omegaMap.{u} n).app (op ⦋m⦌)) := by
  rcases cone_simplex_base_or_tip n (op ⦋m⦌) x with ⟨z, hzx⟩ | ⟨y, hyx, _⟩
  · have h := hx 0
    rw [← hzx, vertex_naturality] at h
    rw [zeroSimplex_unique ((Δ[0] : SSet.{u}).map
      (SimplexCategory.const ⦋0⦌ ⦋m⦌ (0 : Fin (m + 1))).op z)] at h
    change alpha n = omega n at h
    exact False.elim (alpha_ne_omega n h)
  · have hy : ∀ i : Fin (m + 1), y i = Fin.last (n + 1) := by
      intro i
      by_contra hi
      have h := hx i
      rw [← hyx, vertex_naturality] at h
      change (simplexIncl n).app _ (SSet.stdSimplex.obj₀Equiv.symm (y i)) = omega n at h
      rw [simplexIncl_vertex_preLast n (y i) hi] at h
      exact alpha_ne_omega n h
    have hyr : y ∈ (SSet.Subcomplex.range (lastVertex.{u} n)).obj (op ⦋m⦌) := by
      rw [lastVertex_range, SSet.stdSimplex.mem_face_iff]
      simpa only [Finset.mem_singleton] using hy
    obtain ⟨z, hz⟩ := hyr
    refine ⟨z, ?_⟩
    change (simplexIncl n).app _ ((lastVertex n).app _ z) = x
    rw [hz, hyx]

end
end DaggerActualRightConePointSupport
