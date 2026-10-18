import OriginalStrictDaggerGroupoidMappingAction

/-!
# Ebullet C2 mappings into the original strict dagger groupoid

Use the same enriched mapping functor on the actual original Hom action. These
mapping objects are Kan and preserve local weak equivalences of original dagger
maps. The original localization gives a natural full mapping isomorphism to the
previously constructed completed mapping object. The model-category derived Hom
identification of the paper remains a separate obligation.
-/

set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra DaggerModels
open DaggerOriginalDaggerRealizationC2Action DaggerOriginalEC2SimplicialAction
open DaggerOriginalSimplicialGroupoidCompletionUniversal
open DaggerOriginalStrictDaggerGroupoidMappingAction
open DaggerOriginalCompletedDaggerMappingAction DaggerOriginalCompletedDaggerDerivedMapping
open DaggerOriginalSimplicialEquivariantEnrichedAdjunction
open DaggerOriginalSimplicialEquivariantEnrichedQuillen
open scoped SSet.modelCategoryQuillen DaggerOriginalSimplicialActionModelCategory
universe u

namespace DaggerOriginalStrictDaggerGroupoidDerivedMapping

noncomputable section

/-- The exact Ebullet C2 enriched mapping object into the original strict groupoid Hom action. -/
def strictDerivedMapping (C : DaggerSimplicialCat.{u, u})
    (hC : IsStrictGroupoid C.toSimplicialCat) (x y : C.Obj) : SSet.{u} :=
  enrichedMapping simplicialAction (strictMappingAction C hC x y)

/-- The mapping object into the unchanged original Hom is Kan, without an added Kan premise. -/
theorem strictDerivedMapping_kan (C : DaggerSimplicialCat.{u, u})
    (hC : IsStrictGroupoid C.toSimplicialCat) (x y : C.Obj) :
    (strictDerivedMapping C hC x y).KanComplex := by
  have : IsFibrant (strictMappingAction C hC x y) := strictMappingAction_fibrant C hC x y
  exact enrichedMapping_kan simplicialAction _

/-- The actual original dagger Hom map induces the actual equivariant enriched mapping map. -/
def strictDerivedMappingMap {C D : DaggerSimplicialCat.{u, u}}
    (hC : IsStrictGroupoid C.toSimplicialCat) (hD : IsStrictGroupoid D.toSimplicialCat)
    (F : C ⟶ D) (x y : C.Obj) :
    strictDerivedMapping C hC x y ⟶ strictDerivedMapping D hD (F.obj x) (F.obj y) :=
  enrichedMappingMap simplicialAction (strictMappingActionMap hC hD F x y)

/-- A weak equivalence of these exact original Homs induces a weak equivalence of Ebullet maps. -/
theorem strictDerivedMappingMap_weakEquivalence {C D : DaggerSimplicialCat.{u, u}}
    (hC : IsStrictGroupoid C.toSimplicialCat) (hD : IsStrictGroupoid D.toSimplicialCat)
    (F : C ⟶ D) (x y : C.Obj) [WeakEquivalence (F.map x y)] :
    WeakEquivalence (strictDerivedMappingMap hC hD F x y) := by
  have : IsFibrant (strictMappingAction C hC x y) := strictMappingAction_fibrant C hC x y
  have : IsFibrant (strictMappingAction D hD (F.obj x) (F.obj y)) :=
    strictMappingAction_fibrant D hD (F.obj x) (F.obj y)
  have : WeakEquivalence (strictMappingActionMap hC hD F x y) :=
    (DaggerOriginalSimplicialActionModelCategory.weakEquivalence_iff_underlying _).2
      (inferInstanceAs (WeakEquivalence (F.map x y)))
  exact originalEC2_enrichedMapping_map_weakEquivalence (strictMappingActionMap hC hD F x y)

/-- The actual localization-induced map from original to completed equivariant mappings. -/
def strictDerivedMappingLocalizationMap (C : DaggerSimplicialCat.{u, u})
    (hC : IsStrictGroupoid C.toSimplicialCat) (x y : C.Obj) :
    strictDerivedMapping C hC x y ⟶ completedDerivedMapping C x y :=
  enrichedMappingMap simplicialAction (strictLocalizationActionMap C hC x y)

/-- The same original localization gives a full isomorphism of these exact mapping objects. -/
def strictDerivedMappingLocalizationIso (C : DaggerSimplicialCat.{u, u})
    (hC : IsStrictGroupoid C.toSimplicialCat) (x y : C.Obj) :
    strictDerivedMapping C hC x y ≅ completedDerivedMapping C x y :=
  (enrichedMappingFunctor simplicialAction).mapIso (strictLocalizationActionIso C hC x y)

/-- The forward map of this isomorphism is exactly the original localization-induced map. -/
theorem strictDerivedMappingLocalizationIso_hom (C : DaggerSimplicialCat.{u, u})
    (hC : IsStrictGroupoid C.toSimplicialCat) (x y : C.Obj) :
    (strictDerivedMappingLocalizationIso C hC x y).hom =
      strictDerivedMappingLocalizationMap C hC x y := rfl

/-- Native weak equivalence of the exact original-to-completed mapping comparison. -/
theorem strictDerivedMappingLocalizationMap_weakEquivalence (C : DaggerSimplicialCat.{u, u})
    (hC : IsStrictGroupoid C.toSimplicialCat) (x y : C.Obj) :
    WeakEquivalence (strictDerivedMappingLocalizationMap C hC x y) := by
  rw [← strictDerivedMappingLocalizationIso_hom]
  infer_instance

/-- Naturality retains the same original dagger maps and both endpoint labels. -/
theorem strictDerivedMappingLocalizationMap_naturality {C D : DaggerSimplicialCat.{u, u}}
    (hC : IsStrictGroupoid C.toSimplicialCat) (hD : IsStrictGroupoid D.toSimplicialCat)
    (F : C ⟶ D) (x y : C.Obj) :
    strictDerivedMappingMap hC hD F x y ≫
        strictDerivedMappingLocalizationMap D hD (F.obj x) (F.obj y) =
      strictDerivedMappingLocalizationMap C hC x y ≫ completedDerivedMappingMap F x y := by
  have h := congrArg (enrichedMappingFunctor simplicialAction).map
    (strictLocalizationActionMap_naturality hC hD F x y)
  simpa only [Functor.map_comp] using h

end

end DaggerOriginalStrictDaggerGroupoidDerivedMapping
