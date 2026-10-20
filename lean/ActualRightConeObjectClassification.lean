import OriginalCounitRightConeQZeroFaceIntersectionReconciled
import OriginalCounitRightConeQPushoutSimplexSupportReconciled

/-! Exact two-object classification for the original collapsed-face cone and rigidification. -/

set_option autoImplicit false
open CategoryTheory Opposite Simplicial
open DaggerOriginalCounitRightCone
open DaggerOriginalCounitRightConeQZeroFaceIntersection
open DaggerOriginalCounitRightConeQPushoutSimplexSupport
universe u

namespace DaggerActualRightConeObjectClassification

noncomputable section

/-- Every vertex of the actual pushout cone is one of its two original endpoints. -/
theorem vertex_cases (n : ℕ) (x : (cone.{u} n).obj (op ⦋0⦌)) :
    x = alpha.{u} n ∨ x = omega.{u} n := by
  rcases cone_simplex_base_or_tip n (op ⦋0⦌) x with hb | ht
  · obtain ⟨y, rfl⟩ := hb
    left
    have hy : y = SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 1) := by
      apply SSet.stdSimplex.obj₀Equiv.injective
      apply Fin.ext
      simp only [Equiv.apply_symm_apply]
      omega
    rw [hy]
    rfl
  · obtain ⟨y, hyx, hout⟩ := ht
    have hy : y 0 = Fin.last (n + 1) := by
      by_contra hne
      have hin : y ∈ Set.range ((face.{u} n).app (op ⦋0⦌)) := by
        change y ∈ (SSet.Subcomplex.range
          (SSet.stdSimplex.δ (Fin.last (n + 1)) : (Δ[n] : SSet.{u}) ⟶ Δ[n + 1])).obj
            (op ⦋0⦌)
        rw [SSet.stdSimplex.range_δ, SSet.stdSimplex.mem_face_iff]
        intro j
        have hj : j = 0 := by
          apply Fin.ext
          omega
        subst j
        simpa only [Finset.mem_compl, Finset.mem_singleton] using hne
      exact hout hin
    right
    rw [← hyx]
    change (simplexIncl.{u} n).app (op ⦋0⦌) y =
      (simplexIncl.{u} n).app (op ⦋0⦌)
        ((lastVertex.{u} n).app (op ⦋0⦌) (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 1)))
    have hylast : y = (lastVertex.{u} n).app (op ⦋0⦌)
        (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 1)) := by
      apply SSet.stdSimplex.obj₀Equiv.injective
      exact hy
    exact congrArg ((simplexIncl.{u} n).app (op ⦋0⦌)) hylast

/-- The two original endpoints, rather than a quotient of the target objects, label the cone. -/
def vertexEquiv (n : ℕ) : Bool ≃ (cone.{u} n).obj (op ⦋0⦌) :=
  Equiv.ofBijective (fun b ↦ if b then omega.{u} n else alpha.{u} n) (by
    constructor
    · intro b c h
      cases b <;> cases c
      · rfl
      · exact False.elim (alpha_ne_omega n h)
      · exact False.elim (alpha_ne_omega n h.symm)
      · rfl
    · intro x
      rcases vertex_cases n x with h | h
      · exact ⟨false, h.symm⟩
      · exact ⟨true, h.symm⟩)

/-- Pass to the objects of the same original rigidification using its original vertex bijection. -/
def objectEquiv (n : ℕ) :
    Bool ≃ (DaggerModels.OrdinaryRigidification.rigidification.{u}.obj (cone.{u} n)).Obj :=
  (vertexEquiv.{u} n).trans
    (DaggerModels.OrdinaryRigidification.RigidificationVertices.vertexEquiv (cone.{u} n))

theorem objectEquiv_false (n : ℕ) : objectEquiv.{u} n false = alphaObj.{u} n := rfl

theorem objectEquiv_true (n : ℕ) : objectEquiv.{u} n true = omegaObj.{u} n := rfl

/-- The object labels remain distinct even when a later cone map identifies their target values. -/
theorem alphaObj_ne_omegaObj (n : ℕ) : alphaObj.{u} n ≠ omegaObj.{u} n := by
  intro h
  have heq : objectEquiv.{u} n false = objectEquiv.{u} n true := h
  exact Bool.false_ne_true ((objectEquiv.{u} n).injective heq)

end
end DaggerActualRightConeObjectClassification
