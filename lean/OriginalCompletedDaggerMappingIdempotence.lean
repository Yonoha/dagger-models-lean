import OriginalStrictGroupoidCompletionIsomorphisms
import OriginalCompletedDaggerDerivedMapping

/-!
# Actual completed equivariant mapping objects are unchanged by repeated completion

The comparison is induced by the original dagger localization map. Its inverse on
underlying Hom is the full dagger identity lift on the completed category. Original
extension uniqueness identifies the completed unit with the unit on completion.
The unchanged action map bundles this full Hom isomorphism equivariantly; the existing
enriched mapping functor carries that exact isomorphism to the actual mapping objects.
-/

set_option autoImplicit false
open CategoryTheory DaggerModels HomotopicalAlgebra
open DaggerOriginalDaggerRealizationC2Action DaggerOriginalEC2SimplicialAction
open DaggerOriginalSimplicialGroupoidCompletionUniversal
open DaggerOriginalSimplicialGroupoidCompletionDagger
open DaggerOriginalSimplicialGroupoidCompletionDaggerFunctor
open DaggerOriginalStrictGroupoidCompletionIsomorphisms
open DaggerOriginalCompletedDaggerMappingAction DaggerOriginalCompletedDaggerDerivedMapping
open DaggerOriginalSimplicialEquivariantEnrichedAdjunction
open scoped SSet.modelCategoryQuillen DaggerOriginalSimplicialActionModelCategory
universe u

namespace DaggerOriginalCompletedDaggerMappingIdempotence

noncomputable section

/-- Whole dagger-functor equality gives heterogeneous equality of the exact dependent Hom maps. -/
theorem daggerFunctor_map_heq {A B : DaggerSimplicialCat.{u, u}} {F G : A ⟶ B}
    (h : F = G) (x y : A.Obj) : HEq (F.map x y) (G.map x y) := by
  cases h
  rfl

/-- The actual localization-induced completed Hom map is a full simplicial isomorphism. -/
def completedLocalizationHomIso (C : DaggerSimplicialCat.{u, u}) (x y : C.Obj) :
    (completedMappingAction C x y).V ≅ (completedMappingAction (daggerCompletion C) x y).V where
  hom := (completedMappingActionMap (daggerLocalization C) x y).hom
  inv := (daggerCompletionRetraction (daggerCompletion C)
    (completion_isStrictGroupoid C.toSimplicialCat)).map x y
  hom_inv_id := by
    have hm := eq_of_heq (daggerFunctor_map_heq (daggerCompletionMap_localization C) x y)
    change (daggerCompletionMap (daggerLocalization C)).map x y ≫ _ = 𝟙 _
    rw [hm]
    exact eq_of_heq (daggerFunctor_map_heq
      (daggerLocalization_retraction (daggerCompletion C)
        (completion_isStrictGroupoid C.toSimplicialCat)) x y)
  inv_hom_id := by
    have hm := eq_of_heq (daggerFunctor_map_heq (daggerCompletionMap_localization C) x y)
    change _ ≫ (daggerCompletionMap (daggerLocalization C)).map x y = 𝟙 _
    rw [hm]
    exact eq_of_heq (daggerFunctor_map_heq
      (daggerRetraction_localization (daggerCompletion C)
        (completion_isStrictGroupoid C.toSimplicialCat)) x y)

/-- The same original unit-induced mapping map is an actual equivariant isomorphism. -/
def completedLocalizationActionIso (C : DaggerSimplicialCat.{u, u}) (x y : C.Obj) :
    completedMappingAction C x y ≅ completedMappingAction (daggerCompletion C) x y :=
  Action.mkIso (completedLocalizationHomIso C x y)
    (completedMappingActionMap (daggerLocalization C) x y).comm

/-- The equivariant isomorphism's forward map is exactly the original induced action map. -/
theorem completedLocalizationActionIso_hom (C : DaggerSimplicialCat.{u, u}) (x y : C.Obj) :
    (completedLocalizationActionIso C x y).hom =
      completedMappingActionMap (daggerLocalization C) x y := rfl

/-- The unchanged original action map induced by localization is a native isomorphism. -/
theorem completedLocalizationActionMap_isIso (C : DaggerSimplicialCat.{u, u}) (x y : C.Obj) :
    IsIso (completedMappingActionMap (daggerLocalization C) x y) := by
  rw [← completedLocalizationActionIso_hom]
  infer_instance

/-- The actual Ebullet C2 enriched mapping functor gives a full mapping isomorphism. -/
def completedDerivedMappingLocalizationIso (C : DaggerSimplicialCat.{u, u}) (x y : C.Obj) :
    completedDerivedMapping C x y ≅ completedDerivedMapping (daggerCompletion C) x y :=
  (enrichedMappingFunctor simplicialAction).mapIso (completedLocalizationActionIso C x y)

/-- Its forward map is the same original derived mapping map of dagger localization. -/
theorem completedDerivedMappingLocalizationIso_hom (C : DaggerSimplicialCat.{u, u})
    (x y : C.Obj) :
    (completedDerivedMappingLocalizationIso C x y).hom =
      completedDerivedMappingMap (daggerLocalization C) x y := rfl

/-- The actual localization-induced equivariant mapping map is a native weak equivalence. -/
theorem completedDerivedMappingLocalizationMap_weakEquivalence
    (C : DaggerSimplicialCat.{u, u}) (x y : C.Obj) :
    WeakEquivalence (completedDerivedMappingMap (daggerLocalization C) x y) := by
  rw [← completedDerivedMappingLocalizationIso_hom]
  infer_instance

end

end DaggerOriginalCompletedDaggerMappingIdempotence
