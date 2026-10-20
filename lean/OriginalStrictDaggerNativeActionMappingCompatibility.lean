import OriginalStrictDaggerObjectFixedActionCategory
import OriginalStrictDaggerGroupoidDerivedMapping

/-!
# The whole original groupoid action has the original mapping action as its Hom action

The native groupoid action obtained from the proved categorical equivalence has the
same original inverse-dagger functor and the same Hom generator as the previously
verified strict mapping action. This connects the full action correspondence with
the actual Ebullet mapping construction, rather than introducing a separate action.
-/

set_option autoImplicit false
open CategoryTheory DaggerModels
open DaggerOriginalDaggerRealizationC2Action
open DaggerOriginalSimplicialGroupoidCompletionUniversal
open DaggerOriginalSimplicialGroupoidCompletionAdjunction
open DaggerOriginalSimplicialDaggerGroupoidCompletionAdjunction
open DaggerOriginalStrictDaggerGroupoidSigma DaggerOriginalStrictDaggerGroupoidMappingAction
open DaggerOriginalStrictGroupoidDaggerInvolutionEquivalence
open DaggerOriginalStrictGroupoidObjectFixedC2Actions
open DaggerOriginalStrictDaggerObjectFixedActionCategory
universe u

namespace DaggerOriginalStrictDaggerNativeActionMappingCompatibility

noncomputable section

/-- The native whole-groupoid C2 action obtained from the exact original dagger structure. -/
def nativeDaggerGroupoidAction (C : DaggerSimplicialCat.{u, u})
    (hC : IsStrictGroupoid C.toSimplicialCat) : Action StrictSimplicialGroupoids.{u} C2.{u} :=
  nativeFixedAction C.toSimplicialCat hC
    (daggerFixedC2Equiv C.toSimplicialCat hC C.daggerStructure)

/-- Its generator is the exact original full inverse-dagger enriched functor. -/
theorem nativeDaggerGroupoidAction_generator (C : DaggerSimplicialCat.{u, u})
    (hC : IsStrictGroupoid C.toSimplicialCat) :
    ((nativeDaggerGroupoidAction C hC).ρ generator).asHom.hom = strictSigmaFunctor C hC :=
  involutionC2Representation_generator C.toSimplicialCat hC
    (involutionOfDagger C.toSimplicialCat hC C.daggerStructure)

/-- The exact dependent native Hom generator agrees with the existing original Hom action. -/
theorem nativeDaggerGroupoidAction_generator_hom (C : DaggerSimplicialCat.{u, u})
    (hC : IsStrictGroupoid C.toSimplicialCat) (x y : C.Obj) :
    HEq (((nativeDaggerGroupoidAction C hC).ρ generator).asHom.hom.map x y)
      (((strictMappingAction C hC x y).ρ generator).asHom) := by
  have h := enrichedFunctor_map_heq (nativeDaggerGroupoidAction_generator C hC) x y
  exact h.trans (heq_of_eq (strictMappingAction_generator C hC x y).symm)

/-- The category equivalence gives exactly this same native action for every original object. -/
theorem strictDaggerFixedActionEquivalence_obj (C : StrictDaggerSimplicialGroupoids.{u}) :
    (strictDaggerFixedActionEquivalence.functor.obj C).obj =
      nativeDaggerGroupoidAction C.obj C.property := rfl

end

end DaggerOriginalStrictDaggerNativeActionMappingCompatibility
