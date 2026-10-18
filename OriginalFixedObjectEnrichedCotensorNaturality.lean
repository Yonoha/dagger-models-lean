import OriginalFixedObjectDaggerCotensorRepresentation

/-!
# All-parameter source naturality of the original enriched cotensor correspondence

Retain the native enriched precomposition map on Mathlib's mapping object and
the literal composition by the same original fixed-object functor. Naturality
holds for every simplicial parameter, without a fibrancy or model hypothesis.
-/

set_option autoImplicit false
open CategoryTheory MonoidalCategory MonoidalClosed Opposite Simplicial DaggerModels
open DaggerOriginalFixedObjectSimplicialCategories DaggerOriginalFixedObjectDaggerCategories
open DaggerOriginalFixedObjectDegreeCategories DaggerOriginalFixedObjectDaggerDegreeCategories
open DaggerOriginalFixedObjectCotensors
universe u

namespace DaggerOriginalFixedObjectEnrichedCotensorNaturality

noncomputable section

/-- Native enriched precomposition is pointwise composition by the same original functor. -/
theorem parameterEquiv_source {O : Type u} {C C' D : FixedSimplicialCategory O}
    (K : SSet.{u}) (F : C' ⟶ C)
    (G : K ⟶ DaggerOriginalFixedObjectSimplicialEnrichment.mapping C D) :
    DaggerOriginalFixedObjectSimplicialEnrichment.parameterEquiv C' D K
      (G ≫ eHomWhiskerRight SSet F D) =
      Functor.HomObj.comp
        (Functor.HomObj.ofNatTrans (DaggerOriginalFixedObjectSimplicialEnrichment.degreewiseMap F))
        (DaggerOriginalFixedObjectSimplicialEnrichment.parameterEquiv C D K G) := by
  apply Functor.HomObj.ext
  funext n k
  apply degreeHom_ext
  intro x y f
  rfl

/-- Currying a precomposed full family retains the literal original composition. -/
theorem familyToCotensor_source {O : Type u} {C C' D : FixedSimplicialCategory O}
    {K : SSet.{u}} (F : C' ⟶ C)
    (G : Functor.HomObj
      (DaggerOriginalFixedObjectSimplicialEnrichment.degreewiseObj C)
      (DaggerOriginalFixedObjectSimplicialEnrichment.degreewiseObj D) K) :
    DaggerOriginalFixedObjectCotensorRepresentation.familyToCotensor
      (Functor.HomObj.comp
        (Functor.HomObj.ofNatTrans (DaggerOriginalFixedObjectSimplicialEnrichment.degreewiseMap F))
        G) = F ≫ DaggerOriginalFixedObjectCotensorRepresentation.familyToCotensor G := by
  apply fixedHom_ext
  intro x y
  change curry _ = F.map x y ≫ curry _
  rw [← curry_natural_left]
  congr 1

/-- The full representing equivalence intertwines native enriched and original precomposition. -/
theorem cotensorHomEquiv_source {O : Type u} {C C' D : FixedSimplicialCategory O}
    (K : SSet.{u}) (F : C' ⟶ C)
    (G : K ⟶ DaggerOriginalFixedObjectSimplicialEnrichment.mapping C D) :
    DaggerOriginalFixedObjectCotensorRepresentation.cotensorHomEquiv C' D K
      (G ≫ eHomWhiskerRight SSet F D) =
      F ≫ DaggerOriginalFixedObjectCotensorRepresentation.cotensorHomEquiv C D K G := by
  change DaggerOriginalFixedObjectCotensorRepresentation.familyToCotensor
    (DaggerOriginalFixedObjectSimplicialEnrichment.parameterEquiv C' D K
      (G ≫ eHomWhiskerRight SSet F D)) = _
  rw [parameterEquiv_source]
  exact familyToCotensor_source F _

/-- The dagger enriched precomposition map is the full original degree dagger composition. -/
theorem daggerParameterEquiv_source {O : Type u} {C C' D : FixedDaggerCategory O}
    (K : SSet.{u}) (F : C' ⟶ C)
    (G : K ⟶ DaggerOriginalFixedObjectDaggerSimplicialEnrichment.mapping C D) :
    DaggerOriginalFixedObjectDaggerSimplicialEnrichment.parameterEquiv C' D K
      (G ≫ eHomWhiskerRight SSet F D) =
      Functor.HomObj.comp
        (Functor.HomObj.ofNatTrans
          (DaggerOriginalFixedObjectDaggerSimplicialEnrichment.degreewiseMap F))
        (DaggerOriginalFixedObjectDaggerSimplicialEnrichment.parameterEquiv C D K G) := by
  apply Functor.HomObj.ext
  funext n k
  apply degreeDaggerHom_ext
  apply degreeHom_ext
  intro x y f
  rfl

/-- Dagger currying retains literal composition by the same original dagger functor. -/
theorem daggerFamilyToCotensor_source {O : Type u} {C C' D : FixedDaggerCategory O}
    {K : SSet.{u}} (F : C' ⟶ C)
    (G : Functor.HomObj
      (DaggerOriginalFixedObjectDaggerSimplicialEnrichment.degreewiseObj C)
      (DaggerOriginalFixedObjectDaggerSimplicialEnrichment.degreewiseObj D) K) :
    DaggerOriginalFixedObjectDaggerCotensorRepresentation.familyToCotensor
      (Functor.HomObj.comp
        (Functor.HomObj.ofNatTrans
          (DaggerOriginalFixedObjectDaggerSimplicialEnrichment.degreewiseMap F)) G) =
      F ≫ DaggerOriginalFixedObjectDaggerCotensorRepresentation.familyToCotensor G := by
  apply fixedDaggerHom_ext
  exact familyToCotensor_source F.underlying
    (DaggerOriginalFixedObjectDaggerCotensorRepresentation.underlyingFamily G)

/-- The full dagger equivalence intertwines native enriched and original precomposition. -/
theorem daggerCotensorHomEquiv_source {O : Type u} {C C' D : FixedDaggerCategory O}
    (K : SSet.{u}) (F : C' ⟶ C)
    (G : K ⟶ DaggerOriginalFixedObjectDaggerSimplicialEnrichment.mapping C D) :
    DaggerOriginalFixedObjectDaggerCotensorRepresentation.cotensorHomEquiv C' D K
      (G ≫ eHomWhiskerRight SSet F D) =
      F ≫ DaggerOriginalFixedObjectDaggerCotensorRepresentation.cotensorHomEquiv C D K G := by
  change DaggerOriginalFixedObjectDaggerCotensorRepresentation.familyToCotensor
    (DaggerOriginalFixedObjectDaggerSimplicialEnrichment.parameterEquiv C' D K
      (G ≫ eHomWhiskerRight SSet F D)) = _
  rw [daggerParameterEquiv_source]
  exact daggerFamilyToCotensor_source F _

end

end DaggerOriginalFixedObjectEnrichedCotensorNaturality
