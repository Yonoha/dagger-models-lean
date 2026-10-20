import OriginalCounitRightConeQCenterSupportReconciled
import ChosenFlagOriginalHomNaturality

/-!
# Center support of the actual original Hom map

The natural flag/original Hom isomorphism converts an original Hom image
back into the same postcomposed necklace quotient. Its canonical center
therefore has whole simplicial support in the actual source map image.
Both target endpoint equalities are retained explicitly.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial EnrichedCategory
open DaggerChosenRigidificationNecklace DaggerOriginalFlagFlankification
open DaggerOriginalCounitRightConeQCenterSupport

universe u

namespace DaggerOriginalFlagMappedCenterSupport

noncomputable section

/-- A postcomposed flag class has its actual center supported in the map image. -/
theorem flagHomMap_center_support {X Y : SSet.{u}} (f : X ⟶ Y)
    (a b : X.obj (op ⦋0⦌)) (n : ℕ)
    (t : (flagHom X a b).obj (op ⦋n⦌)) :
    SSet.Subcomplex.range
      (centerDegreeObj Y (f.app _ a) (f.app _ b) n
        ((flagHomMap f).app (op ⦋n⦌) t)).1.map ≤ SSet.Subcomplex.range f := by
  induction t using Quot.ind with
  | _ p =>
      let p' : Degree Y (f.app _ a) (f.app _ b) n :=
        ⟨(NecklacesOver.postcomp f).obj p.1, p.2⟩
      change SSet.Subcomplex.range
        (centerDegreeObj Y (f.app _ a) (f.app _ b) n (classOf Y _ _ n p')).1.map ≤ _
      apply center_support_of_representative Y _ _ n p'
      exact Subfunctor.range_comp_le p.1.map f

/-- The literal original enriched Hom image has the same support after both endpoint casts. -/
theorem originalHomMap_center_support {X Y : SSet.{u}} (f : X ⟶ Y)
    (a b : X.obj (op ⦋0⦌)) (c d : Y.obj (op ⦋0⦌))
    (ha : f.app (op ⦋0⦌) a = c) (hb : f.app (op ⦋0⦌) b = d)
    (n : ℕ) (t : (RV X a ⟶[SSet.{u}] RV X b).obj (op ⦋n⦌)) :
    SSet.Subcomplex.range
      (centerDegreeObj Y c d n
        ((flagOriginalHomInverse Y c d).app (op ⦋n⦌)
          ((originalChosenHomMap f a b ≫
            targetHomTransport (congrArg (RV Y) ha) (congrArg (RV Y) hb)).app
              (op ⦋n⦌) t))).1.map ≤ SSet.Subcomplex.range f := by
  subst c
  subst d
  change SSet.Subcomplex.range
    (centerDegreeObj Y (f.app _ a) (f.app _ b) n
      ((flagOriginalHomInverse Y (f.app _ a) (f.app _ b)).app (op ⦋n⦌)
        ((originalChosenHomMap f a b).app (op ⦋n⦌) t))).1.map ≤ _
  have h := congrFun (NatTrans.congr_app
    (flagOriginalHomInverse_naturality f a b) (op ⦋n⦌)) t
  change (flagHomMap f).app (op ⦋n⦌)
      ((flagOriginalHomInverse X a b).app (op ⦋n⦌) t) =
    (flagOriginalHomInverse Y (f.app _ a) (f.app _ b)).app (op ⦋n⦌)
      ((originalChosenHomMap f a b).app (op ⦋n⦌) t) at h
  rw [← h]
  exact flagHomMap_center_support f a b n _

end

end DaggerOriginalFlagMappedCenterSupport
