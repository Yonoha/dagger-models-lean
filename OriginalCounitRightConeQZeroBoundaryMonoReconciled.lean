import OriginalCounitRightConeQZeroCenterObstructionReconciled
import OriginalCounitRightConeQMappedCenterSupportReconciled
import OriginalCounitRightConeQCofaceInjectionReconciled
import OriginalCounitRightConeQBoundaryFaceOverlapReconciled

/-!
# Monicity of the literal Q boundary in cosimplicial degree one

Images of the two distinct Q zero cofaces are disjoint because a common
canonical center would be supported only in the two distinct endpoints.
Each individual Q coface is injective by its actual degeneracy retraction.
The existing all-degree boundary face-overlap criterion gives monicity of
the original boundary-indexed colimit comparison in degree one.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerChosenRigidificationNecklace DaggerOriginalFlagFlankification
open DaggerOriginalCounitRightCone DaggerOriginalCounitRightConeQFunctor
open DaggerOriginalCounitRightConeQZeroCenterObstruction
open DaggerOriginalCounitRightConeQMappedCenterSupport
open DaggerOriginalCounitRightConeQCofaceInjection
open DaggerOriginalCounitRightConeQLatching
open DaggerOriginalCounitRightConeQBoundaryMono
open DaggerOriginalCounitRightConeQBoundaryFaceOverlap

universe u

namespace DaggerOriginalCounitRightConeQZeroBoundaryMono

noncomputable section

/-- Actual Q images from the two distinct zero cofaces never coincide. -/
theorem zero_Qcoface_images_ne (i j : Fin 2) (hij : i ≠ j) (r : ℕ)
    (x y : (Q.{u} 0).obj (op ⦋r⦌)) :
    (Qmap.{u} (SimplexCategory.δ i)).app (op ⦋r⦌) x ≠
      (Qmap.{u} (SimplexCategory.δ j)).app (op ⦋r⦌) y := by
  intro heq
  have hi := Qmap_center_support (SimplexCategory.δ i) r x
  have hj := Qmap_center_support (SimplexCategory.δ j) r y
  rw [← heq] at hj
  exact zero_center_common_support_impossible r _ i j hij (le_inf hi hj)

/-- The disjointness statement applies to every actual simplicial degree. -/
theorem zero_Qcoface_images_ne_app (i j : Fin 2) (hij : i ≠ j)
    (q : SimplexCategoryᵒᵖ) (x y : (QFunctor.{u}.obj ⦋0⦌).obj q) :
    (QFunctor.{u}.map (SimplexCategory.δ i)).app q x ≠
      (QFunctor.{u}.map (SimplexCategory.δ j)).app q y := by
  cases q with
  | op d =>
      induction d using SimplexCategory.rec with | _ r
      exact zero_Qcoface_images_ne i j hij r x y

/-- The original Q boundary colimit map is monic in cosimplicial degree one. -/
theorem boundaryQMap_one_mono : Mono (boundaryQMap.{u} 1) := by
  apply (boundaryQMap_mono_iff_face_overlap.{u} 0).2
  intro q i j x y heq
  by_cases hij : i = j
  · subst j
    have hxy := Qcoface_app_injective 0 i q heq
    rw [hxy]
  · exact False.elim (zero_Qcoface_images_ne_app i j hij q x y heq)

end

end DaggerOriginalCounitRightConeQZeroBoundaryMono
