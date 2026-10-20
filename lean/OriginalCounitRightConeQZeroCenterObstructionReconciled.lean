import OriginalCounitRightConeQZeroFaceIntersectionReconciled
import OriginalFlagPointSupportedCentersReconciled

/-!
# No original canonical center in both distinct zero cofaces

The actual canonical center inherits support from each representative. The
two coface images meet only in point images, so a totally nondegenerate
center supported there would identify the distinct literal cone endpoints.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerChosenRigidificationNecklace
open DaggerOriginalFlagFlankification
open DaggerOriginalCounitRightCone
open DaggerOriginalCounitRightConeFunctor
open DaggerOriginalCounitRightConeQCenterSupport
open DaggerOriginalCounitRightConeQZeroFaceIntersection
open DaggerOriginalFlagPointSupportedCenters

universe u

namespace DaggerOriginalCounitRightConeQZeroCenterObstruction

noncomputable section

/-- A canonical center cannot have its whole image in both distinct zero cofaces. -/
theorem zero_center_common_support_impossible (n : ℕ)
    (t : (flagHom (cone.{u} 1) (alpha.{u} 1) (omega.{u} 1)).obj (op ⦋n⦌))
    (i j : Fin 2) (hij : i ≠ j)
    (hsupport : SSet.Subcomplex.range
      (centerDegreeObj (cone.{u} 1) (alpha.{u} 1) (omega.{u} 1) n t).1.map ≤
        SSet.Subcomplex.range (coneMap.{u} (SimplexCategory.δ i)) ⊓
          SSet.Subcomplex.range (coneMap.{u} (SimplexCategory.δ j))) : False := by
  let points : Bool → ((Δ[0] : SSet.{u}) ⟶ cone.{u} 1) :=
    fun b ↦ if b then omegaMap.{u} 1 else alphaMap.{u} 1
  have hp : SSet.Subcomplex.range
      (centerDegreeObj (cone.{u} 1) (alpha.{u} 1) (omega.{u} 1) n t).1.map ≤
        ⨆ b, SSet.Subcomplex.range (points b) := by
    intro q x hx
    have h := (zero_coface_pointwise_common_image_iff i j hij q x).1 (hsupport q hx)
    simp only [Subfunctor.iSup_obj, Subfunctor.range_obj, Set.mem_iUnion]
    rcases h with ha | ho
    · exact ⟨false, ha⟩
    · exact ⟨true, ho⟩
  exact alpha_ne_omega 1 (center_point_supported_endpoints_eq n t points hp)

/-- Original quotient classes represented in distinct zero cofaces cannot coincide. -/
theorem zero_coface_supported_classes_ne (n : ℕ) (i j : Fin 2) (hij : i ≠ j)
    (p q : Degree (cone.{u} 1) (alpha.{u} 1) (omega.{u} 1) n)
    (hp : SSet.Subcomplex.range p.1.map ≤
      SSet.Subcomplex.range (coneMap.{u} (SimplexCategory.δ i)))
    (hq : SSet.Subcomplex.range q.1.map ≤
      SSet.Subcomplex.range (coneMap.{u} (SimplexCategory.δ j))) :
    classOf (cone.{u} 1) (alpha.{u} 1) (omega.{u} 1) n p ≠
      classOf (cone.{u} 1) (alpha.{u} 1) (omega.{u} 1) n q := by
  intro heq
  exact zero_center_common_support_impossible n _ i j hij
    (center_support_of_equal_class _ _ _ n p q heq _ _ hp hq)

end

end DaggerOriginalCounitRightConeQZeroCenterObstruction
