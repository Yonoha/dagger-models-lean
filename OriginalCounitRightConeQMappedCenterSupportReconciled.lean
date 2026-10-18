import OriginalFlagMappedCenterSupportReconciled
import OriginalCounitRightConeQFunctorReconciled

/-!
# Canonical-center support of the literal Q transition

The same original enriched map and its two actual endpoint casts define the
Q transition. Naturality of the selected original Hom/flag isomorphism then
places the canonical center of every Q image inside the literal cone map image.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial EnrichedCategory
open DaggerModels DaggerModels.OrdinaryRigidification
open DaggerChosenRigidificationNecklace DaggerOriginalFlagFlankification
open DaggerOriginalCounitRightCone DaggerOriginalCounitRightConeFunctor
open DaggerOriginalCounitRightConeQFunctor DaggerOriginalFlagMappedCenterSupport

universe u

namespace DaggerOriginalCounitRightConeQMappedCenterSupport

noncomputable section

/-- The literal Q map is the original chosen Hom map followed by the two vertex casts. -/
theorem Qmap_eq_originalChosenHomMap {m n : SimplexCategory} (f : m ⟶ n) :
    Qmap.{u} f =
      originalChosenHomMap (coneMap.{u} f) (alpha.{u} m.len) (omega.{u} m.len) ≫
        targetHomTransport
          (congrArg (RV (cone.{u} n.len)) (alpha_naturality.{u} f))
          (congrArg (RV (cone.{u} n.len)) (omega_naturality.{u} f)) := by
  rw [Qmap_formula]
  unfold originalChosenHomMap
  rw [Category.assoc, targetHomTransport_trans]
  rfl

/-- Every literal Q image has its actual canonical center in the actual cone-map image. -/
theorem Qmap_center_support {m n : SimplexCategory} (f : m ⟶ n) (r : ℕ)
    (x : (Q.{u} m.len).obj (op ⦋r⦌)) :
    SSet.Subcomplex.range
      (centerDegreeObj (cone.{u} n.len) (alpha.{u} n.len) (omega.{u} n.len) r
        ((flagOriginalHomInverse (cone.{u} n.len) (alpha.{u} n.len)
          (omega.{u} n.len)).app (op ⦋r⦌)
            ((Qmap.{u} f).app (op ⦋r⦌) x))).1.map ≤
      SSet.Subcomplex.range (coneMap.{u} f) := by
  rw [Qmap_eq_originalChosenHomMap]
  exact originalHomMap_center_support (coneMap.{u} f)
    (alpha.{u} m.len) (omega.{u} m.len) (alpha.{u} n.len) (omega.{u} n.len)
    (alpha_naturality.{u} f) (omega_naturality.{u} f) r x

end

end DaggerOriginalCounitRightConeQMappedCenterSupport
