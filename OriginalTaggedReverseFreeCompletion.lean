import OriginalTaggedReverseAdjunctions
import DaggerModels.FreeDaggerPushout
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Free anti-involutive completion and the original free dagger functor

The free anti-involutive object is the left Kan extension along the actual
untagged simplex inclusion. Composing with the already defined left adjoint
of the dagger-to-anti-involutive route recovers the original free dagger
functor, by uniqueness of a left adjoint.
-/

set_option autoImplicit false

open CategoryTheory Functor

universe u

namespace DaggerModels.OriginalTaggedReverseFreeCompletion

open DaggerModels.OriginalTaggedReverseSimplex
open TaggedReverseSimplex
open DaggerModels.OriginalTaggedReversePresheafInclusion

/-- Forget the involution but retain the whole original simplicial set. -/
def antiForget : AntiInvolutiveSSet.{u} ⥤ SSet.{u} where
  obj X := X.toSSet
  map f := f.hom

private instance (A : SSet.{u}) :
    simplexInclusion.op.HasPointwiseLeftKanExtension A := fun _ => inferInstance

/-- Free anti-involutive completion of an ordinary simplicial set. -/
noncomputable def freeAnti : SSet.{u} ⥤ AntiInvolutiveSSet.{u} :=
  simplexInclusion.op.lan ⋙ TaggedPresheaf.toAntiInvolutive

/-- Restriction of a tagged presheaf is its underlying simplicial set. -/
def restrictionForgetIso :
    TaggedPresheaf.toAntiInvolutive ⋙ antiForget.{u} ≅
      (Functor.whiskeringLeft _ _ (Type u)).obj simplexInclusion.op :=
  Iso.refl _

/-- The tagged extension, restricted to untagged simplices, is the original set. -/
noncomputable def extensionRestrictionIso :
    AntiInvolutiveSSet.toPresheaf ⋙
      (Functor.whiskeringLeft _ _ (Type u)).obj simplexInclusion.op ≅
        antiForget.{u} :=
  isoWhiskerLeft AntiInvolutiveSSet.toPresheaf restrictionForgetIso.symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight AntiInvolutiveSSet.unitIso.symm antiForget ≪≫
    Functor.leftUnitor antiForget

/-- The literal free anti-involutive completion is left adjoint to forgetting. -/
noncomputable def freeAntiAdjunction : freeAnti.{u} ⊣ antiForget.{u} :=
  ((simplexInclusion.op.lanAdjunction (Type u)).comp
    antiInvolutiveEquivalence.{u}.symm.toAdjunction).ofNatIsoRight
      extensionRestrictionIso

/-- Restricting the actual dagger-to-anti route recovers the original forgetful functor. -/
noncomputable def daggerForgetIso :
    presheafRoute.{u} ⋙ antiForget.{u} ≅ DaggerSSet.forget.{u} :=
  isoWhiskerRight comparisonIso antiForget

/-- Completing freely with a dagger after freely adjoining an involution
is left adjoint to the original simplicial-set forgetful functor. -/
noncomputable def freeViaAntiAdjunction :
    freeAnti.{u} ⋙ OriginalTaggedReverseAdjunctions.leftKan.{u} ⊣
      DaggerSSet.forget.{u} :=
  (freeAntiAdjunction.comp
    OriginalTaggedReverseAdjunctions.leftAdjunction).ofNatIsoRight
      daggerForgetIso

/-- The two-step actual free completion is the existing free dagger functor. -/
noncomputable def freeViaAntiIsoFreeDagger :
    freeAnti.{u} ⋙ OriginalTaggedReverseAdjunctions.leftKan.{u} ≅
      freeDagger.{u} :=
  Adjunction.leftAdjointUniq freeViaAntiAdjunction freeDaggerAdjunction

/-- The same comparison with the concrete pushout free dagger presentation. -/
noncomputable def freeViaAntiIsoPushout :
    freeAnti.{u} ⋙ OriginalTaggedReverseAdjunctions.leftKan.{u} ≅
      FreeDaggerPushout.functor.{u} :=
  Adjunction.leftAdjointUniq freeViaAntiAdjunction FreeDaggerPushout.adjunction

end DaggerModels.OriginalTaggedReverseFreeCompletion
