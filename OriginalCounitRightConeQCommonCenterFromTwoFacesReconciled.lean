import OriginalCounitRightConeQCommonCenterLiftReconciled
import OriginalCounitRightConeQMappedCenterSupportReconciled

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerOriginalCounitRightCone
open DaggerOriginalCounitRightConeFunctor
open DaggerOriginalCounitRightConeQFunctor
open DaggerOriginalCounitRightConeQCommonBaseFace
open DaggerOriginalCounitRightConeQCommonConeImage
open DaggerOriginalCounitRightConeQMappedCenterSupport
open DaggerOriginalCounitRightConeQCommonCenterLift
open DaggerOriginalFlagFlankification
open DaggerChosenRigidificationNecklace

universe u

namespace DaggerOriginalCounitRightConeQCommonCenterFromTwoFaces

noncomputable section

/-- The actual common smaller cone has the intersection image as a
subcomplex, not just at one chosen simplicial degree. -/
theorem commonConeMap_range_eq_inter (n : ℕ) (i j : Fin (n + 3))
    (hij : i ≠ j) :
    SSet.Subcomplex.range (coneMap.{u} (commonBaseHom n i j hij)) =
      SSet.Subcomplex.range (coneMap.{u} (SimplexCategory.δ i)) ⊓
        SSet.Subcomplex.range (coneMap.{u} (SimplexCategory.δ j)) := by
  apply Subfunctor.ext
  funext q
  ext x
  simpa only [Subfunctor.range_obj, Subfunctor.min_obj,
    Set.mem_inter_iff] using
      (commonConeMap_pointwise_range_iff.{u} n i j hij q x)

/-- If an actual Q simplex lies in both distinct coface images, its
canonical original flagged-necklace center has whole map supported in
the image of the common smaller cone. -/
theorem center_support_of_two_Q_cofaces (n d : ℕ)
    (i j : Fin (n + 3)) (hij : i ≠ j)
    (t : (Q.{u} (n + 2)).obj (op ⦋d⦌))
    (xi xj : (Q.{u} (n + 1)).obj (op ⦋d⦌))
    (hi : (Qmap.{u} (SimplexCategory.δ i)).app (op ⦋d⦌) xi = t)
    (hj : (Qmap.{u} (SimplexCategory.δ j)).app (op ⦋d⦌) xj = t) :
    SSet.Subcomplex.range
      (centerDegreeObj (cone.{u} (n + 2)) (alpha.{u} (n + 2))
        (omega.{u} (n + 2)) d
        ((flagOriginalHomInverse (cone.{u} (n + 2))
          (alpha.{u} (n + 2)) (omega.{u} (n + 2))).app (op ⦋d⦌) t)).1.map ≤
      SSet.Subcomplex.range
        (coneMap.{u} (commonBaseHom n i j hij)) := by
  have hleft := Qmap_center_support.{u} (SimplexCategory.δ i) d xi
  have hright := Qmap_center_support.{u} (SimplexCategory.δ j) d xj
  rw [hi] at hleft
  rw [hj] at hright
  rw [commonConeMap_range_eq_inter.{u} n i j hij]
  exact le_inf hleft hright

/-- A two-face class has an actual common-cone degree representative:
the canonical center's code and flag remain unchanged under the lift. -/
def commonCenterLiftOfTwoQFaces (n d : ℕ)
    (i j : Fin (n + 3)) (hij : i ≠ j)
    (t : (Q.{u} (n + 2)).obj (op ⦋d⦌))
    (xi xj : (Q.{u} (n + 1)).obj (op ⦋d⦌))
    (hi : (Qmap.{u} (SimplexCategory.δ i)).app (op ⦋d⦌) xi = t)
    (hj : (Qmap.{u} (SimplexCategory.δ j)).app (op ⦋d⦌) xj = t) :
    Degree (cone.{u} n) (alpha.{u} n) (omega.{u} n) d :=
  supportedDegreeLift n d i j hij
    (centerDegreeObj (cone.{u} (n + 2)) (alpha.{u} (n + 2))
      (omega.{u} (n + 2)) d
      ((flagOriginalHomInverse (cone.{u} (n + 2))
        (alpha.{u} (n + 2)) (omega.{u} (n + 2))).app (op ⦋d⦌) t))
    (center_support_of_two_Q_cofaces n d i j hij t xi xj hi hj)

end

end DaggerOriginalCounitRightConeQCommonCenterFromTwoFaces
