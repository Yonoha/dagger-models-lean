import OriginalCounitRightConeQCommonCenterFromTwoFacesReconciled
import OriginalFlagFixedEndpointPostcompReconciled

/-!
# Exact original quotient recovery from the common cone lift

The lifted original necklace has the same code and flag and recovers the
same entire map. The existing natural original Hom/flag isomorphism then
gives an actual common Q preimage, with both cone endpoint casts retained.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerChosenRigidificationNecklace DaggerOriginalFlagFlankification
open DaggerOriginalCounitRightCone DaggerOriginalCounitRightConeFunctor
open DaggerOriginalCounitRightConeQFunctor
open DaggerOriginalCounitRightConeQCommonBaseFace
open DaggerOriginalCounitRightConeQCommonCenterLift
open DaggerOriginalCounitRightConeQCommonCenterFromTwoFaces
open DaggerOriginalCounitRightConeQMappedCenterSupport
open DaggerOriginalFlagFixedEndpointPostcomp

universe u

namespace DaggerOriginalCounitRightConeQCommonLiftClass

noncomputable section

/-- Postcomposition recovers the same original degree object, including its full flag. -/
theorem supportedDegreeLift_postcomp (n d : ℕ) (i j : Fin (n + 3)) (hij : i ≠ j)
    (p : Degree (cone.{u} (n + 2)) (alpha.{u} (n + 2)) (omega.{u} (n + 2)) d)
    (hp : SSet.Subcomplex.range p.1.map ≤
      SSet.Subcomplex.range (coneMap.{u} (commonBaseHom n i j hij))) :
    fixedPostcompDegree (coneMap.{u} (commonBaseHom n i j hij))
      (alpha.{u} n) (omega.{u} n) (alpha.{u} (n + 2)) (omega.{u} (n + 2))
      (alpha_naturality (commonBaseHom n i j hij))
      (omega_naturality (commonBaseHom n i j hij)) d
      (supportedDegreeLift n d i j hij p hp) = p := by
  have hm := supportedDegreeLift_map n d i j hij p hp
  refine Sigma.ext ?_ (HEq.rfl)
  cases p with
  | mk P F =>
      cases P with
      | mk T f hfirst hlast =>
          dsimp only [fixedPostcompDegree, supportedDegreeLift]
          congr 1

/-- Actual Q transitions take the original flag class to its literal postcomposed class. -/
theorem Qmap_flagClass {m n : SimplexCategory} (f : m ⟶ n) (d : ℕ)
    (p : Degree (cone.{u} m.len) (alpha.{u} m.len) (omega.{u} m.len) d) :
    (Qmap.{u} f).app (op ⦋d⦌)
      ((flagOriginalHomIso (cone.{u} m.len) (alpha.{u} m.len) (omega.{u} m.len)).hom.app
        (op ⦋d⦌) (classOf _ _ _ d p)) =
      (flagOriginalHomIso (cone.{u} n.len) (alpha.{u} n.len) (omega.{u} n.len)).hom.app
        (op ⦋d⦌)
        (classOf _ _ _ d (fixedPostcompDegree (coneMap.{u} f)
          (alpha.{u} m.len) (omega.{u} m.len) (alpha.{u} n.len) (omega.{u} n.len)
          (alpha_naturality f) (omega_naturality f) d p)) := by
  have h := fixedFlagHomMap_original_naturality (coneMap.{u} f)
    (alpha.{u} m.len) (omega.{u} m.len) (alpha.{u} n.len) (omega.{u} n.len)
    (alpha_naturality f) (omega_naturality f)
  rw [← Qmap_eq_originalChosenHomMap f] at h
  have hh := congrFun (NatTrans.congr_app h (op ⦋d⦌)) (classOf _ _ _ d p)
  change (flagOriginalHomIso _ _ _).hom.app _
    ((fixedFlagHomMap _ _ _ _ _ _ _).app _ (classOf _ _ _ d p)) =
      (Qmap.{u} f).app _ ((flagOriginalHomIso _ _ _).hom.app _ (classOf _ _ _ d p)) at hh
  rw [fixedFlagHomMap_class] at hh
  exact hh.symm

/-- A simplex in two distinct actual Q cofaces has a preimage in the actual common Q. -/
theorem two_Q_cofaces_common_preimage (n d : ℕ) (i j : Fin (n + 3)) (hij : i ≠ j)
    (t : (Q.{u} (n + 2)).obj (op ⦋d⦌))
    (xi xj : (Q.{u} (n + 1)).obj (op ⦋d⦌))
    (hi : (Qmap.{u} (SimplexCategory.δ i)).app (op ⦋d⦌) xi = t)
    (hj : (Qmap.{u} (SimplexCategory.δ j)).app (op ⦋d⦌) xj = t) :
    ∃ z : (Q.{u} n).obj (op ⦋d⦌),
      (Qmap.{u} (commonBaseHom n i j hij)).app (op ⦋d⦌) z = t := by
  let p := centerDegreeObj (cone.{u} (n + 2)) (alpha.{u} (n + 2))
    (omega.{u} (n + 2)) d ((flagOriginalHomInverse _ _ _).app (op ⦋d⦌) t)
  have hp := center_support_of_two_Q_cofaces n d i j hij t xi xj hi hj
  let pl := supportedDegreeLift n d i j hij p hp
  refine ⟨(flagOriginalHomIso (cone.{u} n) (alpha.{u} n) (omega.{u} n)).hom.app
    (op ⦋d⦌) (classOf _ _ _ d pl), ?_⟩
  refine (Qmap_flagClass (commonBaseHom n i j hij) d pl).trans ?_
  change (flagOriginalHomIso _ _ _).hom.app _
    (classOf _ _ _ d (fixedPostcompDegree _ _ _ _ _ _ _ d
      (supportedDegreeLift n d i j hij p hp))) = t
  rw [supportedDegreeLift_postcomp n d i j hij p hp]
  dsimp only [p]
  rw [centerDegreeObj_class]
  exact flagOriginalHomIso_apply_inverse _ _ _ _ t

end

end DaggerOriginalCounitRightConeQCommonLiftClass
