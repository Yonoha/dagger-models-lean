import OriginalSimplicialGroupoidCompletionAdjunction
import OriginalSimplicialDaggerGroupoidCompletionUniversal

/-!
# The original completion fixes strict groupoids and is naturally idempotent

Construct both inverses from the already proved full extension equivalences. Their
components are the original localization and the lift of the original identity. This
retains every object, Hom simplex, dagger and original functor map. No model structure
or localization weak-equivalence hypothesis is used.
-/

set_option autoImplicit false
open CategoryTheory DaggerModels
open DaggerOriginalSimplicialGroupoidCompletion
open DaggerOriginalSimplicialGroupoidCompletionFunctor
open DaggerOriginalSimplicialGroupoidCompletionUniversal
open DaggerOriginalSimplicialGroupoidCompletionAdjunction
open DaggerOriginalSimplicialGroupoidCompletionDagger
open DaggerOriginalSimplicialGroupoidCompletionDaggerFunctor
open DaggerOriginalSimplicialDaggerGroupoidCompletionUniversal
universe u

namespace DaggerOriginalStrictGroupoidCompletionIsomorphisms

noncomputable section

/-- Lift the unchanged identity of a strict original simplicial groupoid. -/
def completionRetraction (C : SimplicialCat.{u, u}) (hC : IsStrictGroupoid C) :
    completion C ⟶ C := lift hC (𝟙 C)

/-- The original localization followed by the identity lift is the original identity. -/
theorem localization_retraction (C : SimplicialCat.{u, u}) (hC : IsStrictGroupoid C) :
    localization C ≫ completionRetraction C hC = 𝟙 C := lift_spec hC (𝟙 C)

/-- Uniqueness on all original Hom maps proves the other inverse identity. -/
theorem retraction_localization (C : SimplicialCat.{u, u}) (hC : IsStrictGroupoid C) :
    completionRetraction C hC ≫ localization C = 𝟙 (completion C) := by
  apply (completionHomEquiv C (completion C) (completion_isStrictGroupoid C)).injective
  change localization C ≫ (completionRetraction C hC ≫ localization C) = localization C ≫ 𝟙 _
  rw [← Category.assoc, localization_retraction, Category.id_comp, Category.comp_id]

/-- The actual localization of a strict simplicial groupoid is a full enriched isomorphism. -/
def localizationIso (C : SimplicialCat.{u, u}) (hC : IsStrictGroupoid C) : C ≅ completion C where
  hom := localization C
  inv := completionRetraction C hC
  hom_inv_id := localization_retraction C hC
  inv_hom_id := retraction_localization C hC

/-- Register the unchanged localization map as a native isomorphism. -/
theorem localization_isIso (C : SimplicialCat.{u, u}) (hC : IsStrictGroupoid C) :
    IsIso (localization C) := by
  change IsIso (localizationIso C hC).hom
  infer_instance

/-- The original completion functor is naturally idempotent on all full simplicial maps. -/
def completionIdempotentIso :
    completionFunctor.{u} ⋙ completionFunctor.{u} ≅ completionFunctor.{u} :=
  NatIso.ofComponents
    (fun C ↦ (localizationIso (completion C) (completion_isStrictGroupoid C)).symm) (by
      intro C D F
      apply (completionHomEquiv (completion C) (completion D)
        (completion_isStrictGroupoid D)).injective
      change localization (completion C) ≫
          (completionMap (completionMap F) ≫ completionRetraction _ _) =
        localization (completion C) ≫ (completionRetraction _ _ ≫ completionMap F)
      rw [← Category.assoc, localization_naturality, Category.assoc,
        localization_retraction, Category.comp_id, ← Category.assoc,
        localization_retraction, Category.id_comp])

/-- Lift the unchanged identity as a full dagger functor. -/
def daggerCompletionRetraction (C : DaggerSimplicialCat.{u, u})
    (hC : IsStrictGroupoid C.toSimplicialCat) : daggerCompletion C ⟶ C := daggerLift hC (𝟙 C)

/-- The actual dagger localization and identity lift compose to the original identity. -/
theorem daggerLocalization_retraction (C : DaggerSimplicialCat.{u, u})
    (hC : IsStrictGroupoid C.toSimplicialCat) :
    daggerLocalization C ≫ daggerCompletionRetraction C hC = 𝟙 C := daggerLift_spec hC (𝟙 C)

/-- Full dagger extension uniqueness proves the second inverse identity. -/
theorem daggerRetraction_localization (C : DaggerSimplicialCat.{u, u})
    (hC : IsStrictGroupoid C.toSimplicialCat) :
    daggerCompletionRetraction C hC ≫ daggerLocalization C = 𝟙 (daggerCompletion C) := by
  apply (daggerCompletionHomEquiv C (daggerCompletion C)
    (completion_isStrictGroupoid C.toSimplicialCat)).injective
  change daggerLocalization C ≫ (daggerCompletionRetraction C hC ≫ daggerLocalization C) =
    daggerLocalization C ≫ 𝟙 _
  rw [← Category.assoc, daggerLocalization_retraction, Category.id_comp, Category.comp_id]

/-- The unchanged dagger localization of a strict target is a full dagger isomorphism. -/
def daggerLocalizationIso (C : DaggerSimplicialCat.{u, u})
    (hC : IsStrictGroupoid C.toSimplicialCat) : C ≅ daggerCompletion C where
  hom := daggerLocalization C
  inv := daggerCompletionRetraction C hC
  hom_inv_id := daggerLocalization_retraction C hC
  inv_hom_id := daggerRetraction_localization C hC

/-- Register the actual dagger localization map as a native isomorphism. -/
theorem daggerLocalization_isIso (C : DaggerSimplicialCat.{u, u})
    (hC : IsStrictGroupoid C.toSimplicialCat) : IsIso (daggerLocalization C) := by
  change IsIso (daggerLocalizationIso C hC).hom
  infer_instance

/-- The actual dagger completion is naturally idempotent, retaining all original dagger maps. -/
def daggerCompletionIdempotentIso :
    daggerCompletionFunctor.{u} ⋙ daggerCompletionFunctor.{u} ≅ daggerCompletionFunctor.{u} :=
  NatIso.ofComponents (fun C ↦ (daggerLocalizationIso (daggerCompletion C)
    (completion_isStrictGroupoid C.toSimplicialCat)).symm) (by
      intro C D F
      apply (daggerCompletionHomEquiv (daggerCompletion C) (daggerCompletion D)
        (completion_isStrictGroupoid D.toSimplicialCat)).injective
      change daggerLocalization (daggerCompletion C) ≫
          (daggerCompletionMap (daggerCompletionMap F) ≫ daggerCompletionRetraction _ _) =
        daggerLocalization (daggerCompletion C) ≫
          (daggerCompletionRetraction _ _ ≫ daggerCompletionMap F)
      rw [← Category.assoc, daggerLocalization_naturality, Category.assoc,
        daggerLocalization_retraction, Category.comp_id, ← Category.assoc,
        daggerLocalization_retraction, Category.id_comp])

/-- The two actual ordinary unit maps into double completion agree on the entire functor. -/
theorem completionMap_localization (C : SimplicialCat.{u, u}) :
    completionMap (localization C) = localization (completion C) := by
  apply (completionHomEquiv C (completion (completion C))
    (completion_isStrictGroupoid (completion C))).injective
  exact localization_naturality (localization C)

/-- The two actual dagger unit maps agree on every object and full dagger Hom map. -/
theorem daggerCompletionMap_localization (C : DaggerSimplicialCat.{u, u}) :
    daggerCompletionMap (daggerLocalization C) = daggerLocalization (daggerCompletion C) := by
  apply (daggerCompletionHomEquiv C (daggerCompletion (daggerCompletion C))
    (completion_isStrictGroupoid (completion C.toSimplicialCat))).injective
  exact daggerLocalization_naturality (daggerLocalization C)

end

end DaggerOriginalStrictGroupoidCompletionIsomorphisms
