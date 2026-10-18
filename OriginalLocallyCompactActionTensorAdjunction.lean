import OriginalLocallyCompactTensorAdjunction
import OriginalActionAdjunctionLift

/-!
# The original locally compact parameter adjunction on C₂ actions

The ordinary tensor and the existing right adjoint act on the original action
through their native functor maps. The lifted unit and counit keep the exact
underlying adjunction. This supplies the native parametrized lifting theorem
on the literal action category.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open DaggerOriginalDaggerRealizationC2Action DaggerOriginalActionAdjunctionLift
open DaggerOriginalLocallyCompactTensorAdjunction

universe u

namespace DaggerOriginalLocallyCompactActionTensorAdjunction

noncomputable section

/-- The existing ordinary tensor applied to the literal C₂ action in its second variable. -/
def locallyCompactActionTensor :
    LocallyCompactTopCat.{u} ⥤ Action TopCat.{u} C2.{u} ⥤ Action TopCat.{u} C2.{u} :=
  locallyCompactTensor ⋙ actionLift C2

/-- The existing right adjoint with the literal postcomposition action. -/
def locallyCompactActionIhom :
    LocallyCompactTopCat.{u}ᵒᵖ ⥤ Action TopCat.{u} C2.{u} ⥤ Action TopCat.{u} C2.{u} :=
  locallyCompactIhom ⋙ actionLift C2

/-- The native parameter adjunction lifts to the original actions. -/
def locallyCompactActionAdjunction :
    locallyCompactActionTensor.{u} ⊣₂ locallyCompactActionIhom.{u} :=
  ParametrizedAdjunction.mk'
    (fun K ↦ actionAdjunction C2 (locallyCompactAdjunction.adj K)) (by
      intro A B i E X f
      apply Action.Hom.ext
      change (locallyCompactAdjunction.adj A).homEquiv E.V X.V
          ((locallyCompactTensor.map i).app E.V ≫ f.hom) =
        (locallyCompactAdjunction.adj B).homEquiv E.V X.V f.hom ≫
          (locallyCompactIhom.map i.op).app X.V
      exact locallyCompactAdjunction.homEquiv_naturality_one i f.hom)

/-- The native pushout-tensor and relative-function-map lifting problems are equivalent. -/
theorem actionPushout_lifting_iff {A B : LocallyCompactTopCat.{u}} (i : A ⟶ B)
    {E F X Y : Action TopCat.{u} C2.{u}} (j : E ⟶ F) (p : X ⟶ Y)
    (h : Functor.PushoutObjObj locallyCompactActionTensor i j)
    (r : Functor.PullbackObjObj locallyCompactActionIhom i p) :
    HasLiftingProperty h.ι p ↔ HasLiftingProperty j r.π :=
  locallyCompactActionAdjunction.hasLiftingProperty_iff h r

/-- The underlying relative function square is the existing native TopCat pullback. -/
def underlyingActionPullback {A B : LocallyCompactTopCat.{u}} (i : A ⟶ B)
    {X Y : Action TopCat.{u} C2.{u}} (p : X ⟶ Y)
    (r : Functor.PullbackObjObj locallyCompactActionIhom i p) :
    Functor.PullbackObjObj locallyCompactIhom i p.hom where
  pt := r.pt.V
  fst := r.fst.hom
  snd := r.snd.hom
  isPullback := r.isPullback.map (Action.forget TopCat C2)

/-- Forgetting the relative-function arrow retains its actual native projection. -/
theorem underlyingActionPullback_π {A B : LocallyCompactTopCat.{u}} (i : A ⟶ B)
    {X Y : Action TopCat.{u} C2.{u}} (p : X ⟶ Y)
    (r : Functor.PullbackObjObj locallyCompactActionIhom i p) :
    (underlyingActionPullback i p r).π = r.π.hom := by
  apply (underlyingActionPullback i p r).isPullback.hom_ext
  · exact (Functor.PullbackObjObj.π_fst _).trans
      (congrArg Action.Hom.hom r.π_fst).symm
  · exact (Functor.PullbackObjObj.π_snd _).trans
      (congrArg Action.Hom.hom r.π_snd).symm

end

end DaggerOriginalLocallyCompactActionTensorAdjunction
