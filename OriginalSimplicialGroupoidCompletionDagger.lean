import OriginalSimplicialGroupoidCompletionSigma

/-!
# The original dagger extends over the actual groupoid completion

Use native degreewise inversion and the proved full covariant involution to equip the
unchanged completion with the existing dagger simplicial structure. The localization
is an actual dagger simplicial functor and agrees with the original dagger on every
original arrow. No mapping-space fibrancy or model-category hypothesis is used.
-/

set_option autoImplicit false

open CategoryTheory MonoidalCategory Opposite Simplicial
open DaggerModels DaggerOriginalSimplicialDegreeCategory
open DaggerOriginalSimplicialDaggerDegreeLaws
open DaggerOriginalSimplicialGroupoidCompletion
open DaggerOriginalSimplicialGroupoidCompletionSigma

universe u

namespace DaggerOriginalSimplicialGroupoidCompletionDagger

noncomputable section

/-- Native inversion is simplicial on the same actual completed Hom. -/
def completedInversionHom (C : SimplicialCat.{u, u}) (x y : C.Obj) :
    completedHom C x y ⟶ completedHom C y x where
  app _ f := inv f
  naturality _ _ i := by
    funext f
    exact ((FreeGroupoid.map (degreeMap C i)).map_inv f).symm

/-- Native degreewise inversion squares to the identity on the whole completed Hom. -/
theorem completedInversionHom_involutive (C : SimplicialCat.{u, u}) (x y : C.Obj) :
    completedInversionHom C x y ≫ completedInversionHom C y x = 𝟙 _ := by
  ext n f
  exact IsIso.inv_inv

/-- The extended original dagger is inverse of the full completed covariant involution. -/
def completedDaggerHom (C : DaggerSimplicialCat.{u, u}) (x y : C.Obj) :
    completedHom C.toSimplicialCat x y ⟶ completedHom C.toSimplicialCat y x :=
  completedSigmaHom C x y ≫ completedInversionHom C.toSimplicialCat x y

/-- The completed inverse-dagger formula recovers exactly the same completed involution. -/
theorem inverse_completedDaggerHom (C : DaggerSimplicialCat.{u, u}) (x y : C.Obj) :
    completedDaggerHom C x y ≫ completedInversionHom C.toSimplicialCat y x =
      completedSigmaHom C x y := by
  rw [completedDaggerHom, Category.assoc, completedInversionHom_involutive, Category.comp_id]

/-- The original dagger extends as the existing full enriched dagger structure. -/
def completedDaggerStructure (C : DaggerSimplicialCat.{u, u}) :
    @DaggerSimplicialStructure C.Obj (completion C.toSimplicialCat).enriched := by
  letI : EnrichedCategory SSet.{u} C.Obj := (completion C.toSimplicialCat).enriched
  refine
    { dagger := completedDaggerHom C
      dagger_involutive := ?_
      dagger_id := ?_
      dagger_comp := ?_ }
  · intro x y
    ext n f
    change inv ((completedSigmaDegree C n).map (inv ((completedSigmaDegree C n).map f))) = f
    simp only [CategoryTheory.Functor.map_inv, IsIso.inv_inv]
    have h := CategoryTheory.Functor.congr_hom (completedSigmaDegree_involutive C n) f
    simpa only [eqToHom_refl, Category.id_comp, Category.comp_id,
      CategoryTheory.Functor.comp_map, CategoryTheory.Functor.id_map] using h
  · intro x
    ext n p
    change inv ((completedSigmaDegree C n).map (𝟙 (completedObject C.toSimplicialCat n x))) =
      𝟙 (completedObject C.toSimplicialCat n x)
    simp only [CategoryTheory.Functor.map_id, IsIso.inv_id]
    rfl
  · intro x y z
    ext n ⟨f, g⟩
    change inv ((completedSigmaDegree C n).map (f ≫ g)) =
      inv ((completedSigmaDegree C n).map g) ≫ inv ((completedSigmaDegree C n).map f)
    simp only [CategoryTheory.Functor.map_comp, IsIso.inv_comp]

/-- Complete the original dagger simplicial category without changing its completed Hom. -/
def daggerCompletion (C : DaggerSimplicialCat.{u, u}) : DaggerSimplicialCat.{u, u} :=
  ⟨completion C.toSimplicialCat, completedDaggerStructure C⟩

/-- Forgetting the extended dagger gives exactly the previously constructed completion. -/
theorem daggerCompletion_underlying (C : DaggerSimplicialCat.{u, u}) :
    (daggerCompletion C).toSimplicialCat = completion C.toSimplicialCat := rfl

/-- The original localization preserves the original dagger on every original Hom simplex. -/
def daggerLocalization (C : DaggerSimplicialCat.{u, u}) : C ⟶ daggerCompletion C where
  __ := localization C.toSimplicialCat
  map_dagger x y := by
    ext n f
    change inv ((completedSigmaDegree C n).map ((FreeGroupoid.of _).map f)) =
      (FreeGroupoid.of _).map (degreeDagger C n f)
    simp only [completedSigmaDegree_generator, IsIso.inv_inv]

/-- The actual dagger localization is the unchanged original full simplicial localization. -/
theorem daggerLocalization_underlying (C : DaggerSimplicialCat.{u, u}) :
    (daggerLocalization C).toEnrichedFunctor = localization C.toSimplicialCat := rfl

end

end DaggerOriginalSimplicialGroupoidCompletionDagger
