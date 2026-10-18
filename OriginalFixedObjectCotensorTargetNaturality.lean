import OriginalFixedObjectNativeMappingComparison

/-!
# Full target naturality of the original cotensor representing equivalence

The original degreewise parameter families compose with the entire original
target functor. Native currying gives precisely the original cotensor functor.
This includes all parameters and all simplices of the native enriched Hom.
-/
set_option autoImplicit false
open CategoryTheory MonoidalCategory MonoidalClosed Opposite Simplicial DaggerModels
open DaggerOriginalFixedObjectSimplicialCategories DaggerOriginalFixedObjectDaggerCategories
open DaggerOriginalFixedObjectDegreeCategories DaggerOriginalFixedObjectDaggerDegreeCategories
open DaggerOriginalFixedObjectCotensors
universe u
namespace DaggerOriginalFixedObjectCotensorTargetNaturality
noncomputable section

/-- The full ordinary parameter family is postcomposed by the same original target functor. -/
theorem parameterEquiv_target {O : Type u} (K : SSet.{u})
    (C : FixedSimplicialCategory O) {D E : FixedSimplicialCategory O} (F : D ⟶ E)
    (G : K ⟶ DaggerOriginalFixedObjectSimplicialEnrichment.mapping C D) :
    DaggerOriginalFixedObjectSimplicialEnrichment.parameterEquiv C E K
      (G ≫ eHomWhiskerLeft SSet C F) =
      Functor.HomObj.comp
        (DaggerOriginalFixedObjectSimplicialEnrichment.parameterEquiv C D K G)
        (Functor.HomObj.ofNatTrans
          (DaggerOriginalFixedObjectSimplicialEnrichment.degreewiseMap F)) := by
  apply Functor.HomObj.ext
  funext n k
  apply degreeHom_ext
  intro x y f
  rfl

/-- Native currying retains literal composition with the original target cotensor functor. -/
theorem familyToCotensor_target {O : Type u} {K : SSet.{u}}
    {C D E : FixedSimplicialCategory O} (F : D ⟶ E)
    (G : Functor.HomObj
      (DaggerOriginalFixedObjectSimplicialEnrichment.degreewiseObj C)
      (DaggerOriginalFixedObjectSimplicialEnrichment.degreewiseObj D) K) :
    DaggerOriginalFixedObjectCotensorRepresentation.familyToCotensor
      (Functor.HomObj.comp G (Functor.HomObj.ofNatTrans
        (DaggerOriginalFixedObjectSimplicialEnrichment.degreewiseMap F))) =
      DaggerOriginalFixedObjectCotensorRepresentation.familyToCotensor G ≫
        cotensorMap K F := by
  apply fixedHom_ext
  intro x y
  change curry _ = curry _ ≫ (ihom K).map (F.map x y)
  rw [← curry_natural_right]
  rfl

/-- Dagger parameter families retain full target composition, including all original Hom maps. -/
theorem daggerParameterEquiv_target {O : Type u} (K : SSet.{u})
    (C : FixedDaggerCategory O) {D E : FixedDaggerCategory O} (F : D ⟶ E)
    (G : K ⟶ DaggerOriginalFixedObjectDaggerSimplicialEnrichment.mapping C D) :
    DaggerOriginalFixedObjectDaggerSimplicialEnrichment.parameterEquiv C E K
      (G ≫ eHomWhiskerLeft SSet C F) =
      Functor.HomObj.comp
        (DaggerOriginalFixedObjectDaggerSimplicialEnrichment.parameterEquiv C D K G)
        (Functor.HomObj.ofNatTrans
          (DaggerOriginalFixedObjectDaggerSimplicialEnrichment.degreewiseMap F)) := by
  apply Functor.HomObj.ext
  funext n k
  apply degreeDaggerHom_ext
  apply degreeHom_ext
  intro x y f
  rfl

/-- The full original dagger cotensor correspondence retains exact target composition. -/
theorem daggerFamilyToCotensor_target {O : Type u} {K : SSet.{u}}
    {C D E : FixedDaggerCategory O} (F : D ⟶ E)
    (G : Functor.HomObj
      (DaggerOriginalFixedObjectDaggerSimplicialEnrichment.degreewiseObj C)
      (DaggerOriginalFixedObjectDaggerSimplicialEnrichment.degreewiseObj D) K) :
    DaggerOriginalFixedObjectDaggerCotensorRepresentation.familyToCotensor
      (Functor.HomObj.comp G (Functor.HomObj.ofNatTrans
        (DaggerOriginalFixedObjectDaggerSimplicialEnrichment.degreewiseMap F))) =
      DaggerOriginalFixedObjectDaggerCotensorRepresentation.familyToCotensor G ≫
        daggerCotensorMap K F := by
  apply fixedDaggerHom_ext
  exact familyToCotensor_target F.underlying
    (DaggerOriginalFixedObjectDaggerCotensorRepresentation.underlyingFamily G)

/-- All original parameters of the full dagger representing equivalence are target natural. -/
theorem daggerCotensorHomEquiv_target {O : Type u} (K : SSet.{u})
    (C : FixedDaggerCategory O) {D E : FixedDaggerCategory O} (F : D ⟶ E)
    (G : K ⟶ DaggerOriginalFixedObjectDaggerSimplicialEnrichment.mapping C D) :
    DaggerOriginalFixedObjectDaggerCotensorRepresentation.cotensorHomEquiv C E K
      (G ≫ eHomWhiskerLeft SSet C F) =
      DaggerOriginalFixedObjectDaggerCotensorRepresentation.cotensorHomEquiv C D K G ≫
        daggerCotensorMap K F := by
  change DaggerOriginalFixedObjectDaggerCotensorRepresentation.familyToCotensor
    (DaggerOriginalFixedObjectDaggerSimplicialEnrichment.parameterEquiv C E K
      (G ≫ eHomWhiskerLeft SSet C F)) = _
  rw [daggerParameterEquiv_target]
  exact daggerFamilyToCotensor_target F _

/-- Each native enriched simplex retains the exact original full target cotensor map. -/
theorem daggerSimplexEquiv_target {O : Type u} (C : FixedDaggerCategory O)
    {D E : FixedDaggerCategory O} (F : D ⟶ E) (n : SimplexCategoryᵒᵖ)
    (s : (C ⟶[SSet.{u}] D).obj n) :
    DaggerOriginalFixedObjectNativeMappingComparison.daggerSimplexEquiv C E n
      ((eHomWhiskerLeft SSet C F).app n s) =
      DaggerOriginalFixedObjectNativeMappingComparison.daggerSimplexEquiv C D n s ≫
        daggerCotensorMap (SSet.stdSimplex.obj n.unop) F := by
  change DaggerOriginalFixedObjectDaggerCotensorRepresentation.cotensorHomEquiv C E _
    (SSet.yonedaEquiv.symm ((eHomWhiskerLeft SSet C F).app n s)) = _
  rw [← SSet.yonedaEquiv_symm_comp]
  exact daggerCotensorHomEquiv_target _ C F _

end
end DaggerOriginalFixedObjectCotensorTargetNaturality
