import OriginalSimplicialGroupoidCompletionDagger

/-!
# Functoriality of the actual dagger groupoid completion

The unchanged original completion map of a dagger functor preserves the extended
dagger. This follows from the full native universal property, not from checking
generating arrows alone. The original dagger localizations are natural.
-/

set_option autoImplicit false

open CategoryTheory MonoidalCategory Opposite Simplicial
open DaggerModels DaggerOriginalSimplicialDegreeCategory
open DaggerOriginalSimplicialDaggerDegreeLaws
open DaggerOriginalSimplicialGroupoidCompletion
open DaggerOriginalSimplicialGroupoidCompletionFunctor
open DaggerOriginalSimplicialGroupoidCompletionSigma
open DaggerOriginalSimplicialGroupoidCompletionDagger

universe u

namespace DaggerOriginalSimplicialGroupoidCompletionDaggerFunctor

noncomputable section

/-- Every original dagger functor preserves every original degree dagger. -/
theorem degreeDagger_functor {C D : DaggerSimplicialCat.{u, u}} (F : C ⟶ D)
    (n : SimplexCategoryᵒᵖ) {x y : degreeObjects C.toSimplicialCat n} (f : x ⟶ y) :
    degreeDagger D n ((degreeFunctor F.toEnrichedFunctor n).map f) =
      (degreeFunctor F.toEnrichedFunctor n).map (degreeDagger C n f) :=
  congrFun (NatTrans.congr_app (F.map_dagger x y) n) f

/-- The inverse-dagger seeds commute with every original dagger degree functor. -/
theorem degreeSigmaSeed_functor {C D : DaggerSimplicialCat.{u, u}} (F : C ⟶ D)
    (n : SimplexCategoryᵒᵖ) :
    degreeFunctor F.toEnrichedFunctor n ⋙ degreeSigmaSeed D n =
      degreeSigmaSeed C n ⋙ FreeGroupoid.map (degreeFunctor F.toEnrichedFunctor n) := by
  refine CategoryTheory.Functor.hext
    (F := degreeFunctor F.toEnrichedFunctor n ⋙ degreeSigmaSeed D n)
    (G := degreeSigmaSeed C n ⋙ FreeGroupoid.map (degreeFunctor F.toEnrichedFunctor n))
    (fun _ ↦ rfl) ?_
  intro x y f
  apply heq_of_eq
  change inv ((FreeGroupoid.of _).map
      (degreeDagger D n ((degreeFunctor F.toEnrichedFunctor n).map f))) =
    (FreeGroupoid.map (degreeFunctor F.toEnrichedFunctor n)).map
      (inv ((FreeGroupoid.of _).map (degreeDagger C n f)))
  rw [CategoryTheory.Functor.map_inv]
  change inv ((FreeGroupoid.of _).map
      (degreeDagger D n ((degreeFunctor F.toEnrichedFunctor n).map f))) =
    inv ((FreeGroupoid.of _).map
      ((degreeFunctor F.toEnrichedFunctor n).map (degreeDagger C n f)))
  rw [degreeDagger_functor]

/-- The full completed covariant involutions commute with the original completion map. -/
theorem completedSigmaDegree_functor {C D : DaggerSimplicialCat.{u, u}} (F : C ⟶ D)
    (n : SimplexCategoryᵒᵖ) :
    FreeGroupoid.map (degreeFunctor F.toEnrichedFunctor n) ⋙ completedSigmaDegree D n =
      completedSigmaDegree C n ⋙ FreeGroupoid.map (degreeFunctor F.toEnrichedFunctor n) := by
  change FreeGroupoid.map (degreeFunctor F.toEnrichedFunctor n) ⋙
      FreeGroupoid.lift (degreeSigmaSeed D n) =
    FreeGroupoid.lift (degreeSigmaSeed C n) ⋙
      FreeGroupoid.map (degreeFunctor F.toEnrichedFunctor n)
  rw [FreeGroupoid.map_comp_lift, ← FreeGroupoid.lift_comp, degreeSigmaSeed_functor]

/-- The same original full completion map is a dagger simplicial functor. -/
def daggerCompletionMap {C D : DaggerSimplicialCat.{u, u}} (F : C ⟶ D) :
    daggerCompletion C ⟶ daggerCompletion D where
  __ := completionMap F.toEnrichedFunctor
  map_dagger x y := by
    ext n f
    change inv ((completedSigmaDegree D n).map
        ((FreeGroupoid.map (degreeFunctor F.toEnrichedFunctor n)).map f)) =
      (FreeGroupoid.map (degreeFunctor F.toEnrichedFunctor n)).map
        (inv ((completedSigmaDegree C n).map f))
    have h := CategoryTheory.Functor.congr_hom (completedSigmaDegree_functor F n) f
    have hh : (completedSigmaDegree D n).map
        ((FreeGroupoid.map (degreeFunctor F.toEnrichedFunctor n)).map f) =
      (FreeGroupoid.map (degreeFunctor F.toEnrichedFunctor n)).map
        ((completedSigmaDegree C n).map f) := by
      simpa only [eqToHom_refl, Category.id_comp, Category.comp_id,
        CategoryTheory.Functor.comp_map] using h
    simpa only [CategoryTheory.Functor.map_inv] using congrArg (fun g ↦ inv g) hh

/-- Identity preservation retains exactly the previous full completion identity. -/
theorem daggerCompletionMap_id (C : DaggerSimplicialCat.{u, u}) :
    daggerCompletionMap (𝟙 C) = 𝟙 (daggerCompletion C) := by
  apply DaggerSimplicialCat.Hom.ext
  exact completionMap_id C.toSimplicialCat

/-- Composition preservation retains exactly the previous full completion composition. -/
theorem daggerCompletionMap_comp {C D E : DaggerSimplicialCat.{u, u}}
    (F : C ⟶ D) (G : D ⟶ E) :
    daggerCompletionMap (F ≫ G) = daggerCompletionMap F ≫ daggerCompletionMap G := by
  apply DaggerSimplicialCat.Hom.ext
  exact completionMap_comp F.toEnrichedFunctor G.toEnrichedFunctor

/-- Degreewise groupoid completion is a functor on the original dagger simplicial categories. -/
def daggerCompletionFunctor : DaggerSimplicialCat.{u, u} ⥤ DaggerSimplicialCat.{u, u} where
  obj := daggerCompletion
  map := daggerCompletionMap
  map_id := daggerCompletionMap_id
  map_comp := daggerCompletionMap_comp

/-- The same original dagger localizations are natural on every original dagger functor. -/
theorem daggerLocalization_naturality {C D : DaggerSimplicialCat.{u, u}} (F : C ⟶ D) :
    daggerLocalization C ≫ daggerCompletionMap F = F ≫ daggerLocalization D := by
  apply DaggerSimplicialCat.Hom.ext
  exact localization_naturality F.toEnrichedFunctor

/-- Bundle the actual original dagger localizations into their natural transformation. -/
def daggerLocalizationNatTrans :
    𝟭 DaggerSimplicialCat.{u, u} ⟶ daggerCompletionFunctor.{u} where
  app := daggerLocalization
  naturality _ _ F := (daggerLocalization_naturality F).symm

end

end DaggerOriginalSimplicialGroupoidCompletionDaggerFunctor
