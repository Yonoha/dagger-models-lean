import OriginalStrictDaggerGroupoidSigma
import OriginalCompletedDaggerMappingIdempotence

/-!
# The actual original strict dagger groupoid Hom with its C2 action

The action is on the unchanged original Hom, with generator inverse original dagger.
Original dagger maps give equivariant maps. Localization gives a full equivariant
isomorphism to the existing completed Hom action when the source is strict.
-/

set_option autoImplicit false
open CategoryTheory Opposite Simplicial HomotopicalAlgebra
open DaggerModels DaggerOriginalSimplicialDegreeCategory
open DaggerOriginalSimplicialDaggerDegreeLaws DaggerOriginalStrictDaggerGroupoidSigma
open DaggerOriginalDaggerRealizationC2Action DaggerOriginalCompletedDaggerMappingAction
open DaggerOriginalSimplicialGroupoidCompletionUniversal
open DaggerOriginalSimplicialGroupoidCompletionSigma
open DaggerOriginalSimplicialGroupoidCompletionDagger
open DaggerOriginalSimplicialGroupoidCompletionDaggerFunctor
open DaggerOriginalStrictGroupoidCompletionIsomorphisms
open DaggerOriginalCompletedDaggerMappingIdempotence
open scoped SSet.modelCategoryQuillen DaggerOriginalSimplicialActionModelCategory
universe u

namespace DaggerOriginalStrictDaggerGroupoidMappingAction

noncomputable section

/-- The original strict groupoid Hom with the original group acting by inverse dagger. -/
def strictMappingAction (C : DaggerSimplicialCat.{u, u})
    (hC : IsStrictGroupoid C.toSimplicialCat) (x y : C.Obj) : Action SSet.{u} C2.{u} where
  V := C.toSimplicialCat.enriched.Hom x y
  ρ :=
    { toFun := fun g ↦ if g = 1 then 1 else End.of (strictSigmaHom C hC x y)
      map_one' := by simp
      map_mul' := fun g h ↦ by
        rcases originalC2_cases g with rfl | rfl
        · simp
        rcases originalC2_cases h with rfl | rfl
        · simp
        simp [originalGenerator_mul_self, originalGenerator_ne_one, End.mul_def,
          strictSigmaHom_involutive] }

/-- The generator is precisely the original covariant inverse-dagger map. -/
theorem strictMappingAction_generator (C : DaggerSimplicialCat.{u, u})
    (hC : IsStrictGroupoid C.toSimplicialCat) (x y : C.Obj) :
    ((strictMappingAction C hC x y).ρ generator).asHom = strictSigmaHom C hC x y := by
  simp [strictMappingAction, originalGenerator_ne_one]

/-- Degreewise this is inverse of the original dagger, rather than a replacement dagger. -/
theorem strictMappingAction_generator_degree (C : DaggerSimplicialCat.{u, u})
    (hC : IsStrictGroupoid C.toSimplicialCat) (x y : C.Obj) (n : SimplexCategoryᵒᵖ)
    (f : (C.toSimplicialCat.enriched.Hom x y).obj n) :
    letI := strictDegreeGroupoid C.toSimplicialCat hC n
    (((strictMappingAction C hC x y).ρ generator).asHom).app n f =
      inv (degreeDagger C n f) := by
  rw [strictMappingAction_generator]
  rfl

/-- Every original dagger functor gives the actual equivariant original Hom map. -/
def strictMappingActionMap {C D : DaggerSimplicialCat.{u, u}}
    (hC : IsStrictGroupoid C.toSimplicialCat) (hD : IsStrictGroupoid D.toSimplicialCat)
    (F : C ⟶ D) (x y : C.Obj) :
    strictMappingAction C hC x y ⟶ strictMappingAction D hD (F.obj x) (F.obj y) where
  hom := F.map x y
  comm g := by
    rcases originalC2_cases g with rfl | rfl
    · simp
    · simpa only [strictMappingAction_generator] using strictSigmaHom_functor hC hD F x y

/-- On completion, inverse of its actual extended dagger is the existing completed sigma. -/
theorem strictSigmaHom_completion (C : DaggerSimplicialCat.{u, u}) (x y : C.Obj) :
    strictSigmaHom (daggerCompletion C) (completion_isStrictGroupoid C.toSimplicialCat) x y =
      completedSigmaHom C x y := by
  ext n f
  change inv (inv ((completedSigmaDegree C n).map f)) = (completedSigmaDegree C n).map f
  exact IsIso.inv_inv

/-- The original localization gives an equivariant map to the actual completed Hom action. -/
def strictLocalizationActionMap (C : DaggerSimplicialCat.{u, u})
    (hC : IsStrictGroupoid C.toSimplicialCat) (x y : C.Obj) :
    strictMappingAction C hC x y ⟶ completedMappingAction C x y where
  hom := (daggerLocalization C).map x y
  comm g := by
    rcases originalC2_cases g with rfl | rfl
    · simp
    · have h := strictSigmaHom_functor hC (completion_isStrictGroupoid C.toSimplicialCat)
        (daggerLocalization C) x y
      rw [strictSigmaHom_completion] at h
      simpa only [strictMappingAction_generator, completedMappingAction_generator] using h

/-- The underlying localization is a full Hom isomorphism with its original identity lift. -/
def strictLocalizationHomIso (C : DaggerSimplicialCat.{u, u})
    (hC : IsStrictGroupoid C.toSimplicialCat) (x y : C.Obj) :
    (strictMappingAction C hC x y).V ≅ (completedMappingAction C x y).V where
  hom := (daggerLocalization C).map x y
  inv := (daggerCompletionRetraction C hC).map x y
  hom_inv_id := eq_of_heq (daggerFunctor_map_heq (daggerLocalization_retraction C hC) x y)
  inv_hom_id := eq_of_heq (daggerFunctor_map_heq (daggerRetraction_localization C hC) x y)

/-- The unchanged original localization Hom map is an actual equivariant isomorphism. -/
def strictLocalizationActionIso (C : DaggerSimplicialCat.{u, u})
    (hC : IsStrictGroupoid C.toSimplicialCat) (x y : C.Obj) :
    strictMappingAction C hC x y ≅ completedMappingAction C x y :=
  Action.mkIso (strictLocalizationHomIso C hC x y)
    (strictLocalizationActionMap C hC x y).comm

/-- The equivariant iso retains the precise original localization map as its forward map. -/
theorem strictLocalizationActionIso_hom (C : DaggerSimplicialCat.{u, u})
    (hC : IsStrictGroupoid C.toSimplicialCat) (x y : C.Obj) :
    (strictLocalizationActionIso C hC x y).hom = strictLocalizationActionMap C hC x y := rfl

/-- The actual equivariant localization comparisons are natural in original dagger maps. -/
theorem strictLocalizationActionMap_naturality {C D : DaggerSimplicialCat.{u, u}}
    (hC : IsStrictGroupoid C.toSimplicialCat) (hD : IsStrictGroupoid D.toSimplicialCat)
    (F : C ⟶ D) (x y : C.Obj) :
    strictMappingActionMap hC hD F x y ≫ strictLocalizationActionMap D hD (F.obj x) (F.obj y) =
      strictLocalizationActionMap C hC x y ≫ completedMappingActionMap F x y := by
  apply Action.Hom.ext
  exact eq_of_heq (daggerFunctor_map_heq (daggerLocalization_naturality F).symm x y)

/-- Fibrancy holds on the original strict groupoid action by its original Kan Hom. -/
theorem strictMappingAction_fibrant (C : DaggerSimplicialCat.{u, u})
    (hC : IsStrictGroupoid C.toSimplicialCat) (x y : C.Obj) :
    IsFibrant (strictMappingAction C hC x y) :=
  (DaggerOriginalSimplicialActionModelCategory.isFibrant_iff_underlying _).2
    (DaggerOriginalStrictSimplicialGroupoidMappingKan.strictHom_kan C.toSimplicialCat hC x y)

end

end DaggerOriginalStrictDaggerGroupoidMappingAction
