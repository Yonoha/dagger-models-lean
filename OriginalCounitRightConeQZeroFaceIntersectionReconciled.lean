import OriginalCounitRightConeQCofaceImageIntersectionReconciled
import OriginalCounitRightConeRetractionHomFactorizationReconciled
import ChosenNecklacePointMaps

/-!
# The literal zero-dimensional common cone faces

The two distinct cofaces of the first cone intersect only in the two actual
endpoint point images. The endpoints remain distinct, as detected by the
already constructed projection to the directed interval.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerOriginalCounitRightCone
open DaggerOriginalCounitRightConeFunctor
open DaggerOriginalCounitRightConeQCofaceImageIntersection
open DaggerOriginalCounitRightConeContractibilityRetraction
open DaggerOriginalCounitRightConeRetractionHomFactorization
open DaggerChosenRigidificationNecklace.NecklaceCode

universe u

namespace DaggerOriginalCounitRightConeQZeroFaceIntersection

noncomputable section

/-- The actual last-vertex map is the constant standard-simplex map. -/
theorem lastVertex_eq_const (n : ℕ) :
    lastVertex.{u} n = SSet.stdSimplex.map
      (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ (Fin.last (n + 1))) := by
  apply SSet.yonedaEquiv.injective
  rw [lastVertex, Equiv.apply_symm_apply, SSet.stdSimplex.yonedaEquiv_map]
  rfl

/-- The final vertex image is exactly its singleton face in the large simplex. -/
theorem lastVertex_range (n : ℕ) :
    SSet.Subcomplex.range (lastVertex.{u} n) =
      SSet.stdSimplex.face.{u} {Fin.last (n + 1)} := by
  rw [lastVertex_eq_const]
  ext ⟨d⟩ x
  induction d using SimplexCategory.rec with | _ d
  change (∃ z, (SSet.stdSimplex.map
    (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ (Fin.last (n + 1)))).app
      (op ⦋d⦌) z = x) ↔ _
  rw [SSet.stdSimplex.mem_face_iff]
  constructor
  · rintro ⟨z, rfl⟩ v
    change Fin.last (n + 1) ∈ ({Fin.last (n + 1)} : Finset _)
    simp
  · intro hx
    refine ⟨zeroSimplex d, ?_⟩
    apply SSet.stdSimplex.ext
    intro v
    change Fin.last (n + 1) = x v
    exact (Finset.mem_singleton.mp (hx v)).symm

private theorem zero_common_face_indices (i j : Fin 2) (hij : i ≠ j) :
    ({i.castSucc}ᶜ ⊓ {j.castSucc}ᶜ : Finset (Fin 3)) = {Fin.last 2} := by
  fin_cases i <;> fin_cases j
  · exact False.elim (hij rfl)
  · decide
  · decide
  · exact False.elim (hij rfl)

/-- The distinct zero cofaces meet only in the original two endpoint images. -/
theorem zero_coface_pointwise_common_image_iff (i j : Fin 2) (hij : i ≠ j)
    (q : SimplexCategoryᵒᵖ) (x : (cone.{u} 1).obj q) :
    (x ∈ Set.range ((coneMap.{u} (SimplexCategory.δ i)).app q) ∧
      x ∈ Set.range ((coneMap.{u} (SimplexCategory.δ j)).app q)) ↔
      x ∈ Set.range ((alphaMap.{u} 1).app q) ∨
        x ∈ Set.range ((omegaMap.{u} 1).app q) := by
  rw [coface_pointwise_common_image_iff, zero_common_face_indices i j hij]
  constructor
  · rintro (hb | ⟨y, hy, hyx⟩)
    · exact Or.inl hb
    · have hyr : y ∈ (SSet.Subcomplex.range (lastVertex.{u} 1)).obj q := by
        rw [lastVertex_range]
        exact hy
      obtain ⟨z, hz⟩ := hyr
      refine Or.inr ⟨z, ?_⟩
      change (simplexIncl.{u} 1).app q ((lastVertex.{u} 1).app q z) = x
      rw [hz, hyx]
  · rintro (hb | ⟨z, rfl⟩)
    · exact Or.inl hb
    · refine Or.inr ⟨(lastVertex.{u} 1).app q z, ?_, rfl⟩
      rw [← lastVertex_range]
      exact ⟨z, rfl⟩

/-- The actual collapsed and terminal cone endpoints are distinct in every degree zero. -/
theorem alpha_ne_omega (n : ℕ) : alpha.{u} n ≠ omega.{u} n := by
  intro h
  have hv := congrArg ((projection.{u} n).app (op ⦋0⦌)) h
  rw [projection_alpha, projection_omega] at hv
  have h01 := congrArg (fun x : (Δ[1] : SSet.{u}).obj (op ⦋0⦌) ↦ x 0) hv
  change (0 : Fin 2) = 1 at h01
  exact (by decide : (0 : Fin 2) ≠ 1) h01

end

end DaggerOriginalCounitRightConeQZeroFaceIntersection
