import NativeOriginalC2RealizationMapping
import OriginalEC2EnrichedRealizationSingularComparison
import OriginalSimplicialEquivariantEnrichedQuillen

/-! The exact native unit compares ORIGINAL enriched EC2 maps with literal realized EC2 maps. -/
set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra
open DaggerOriginalDaggerRealizationC2Action DaggerOriginalEC2SimplicialAction
open DaggerOriginalSimplicialEquivariantParameterTensor
open DaggerOriginalSimplicialEquivariantEnrichedAdjunction
open DaggerOriginalSimplicialEquivariantEnrichedQuillen
open DaggerOriginalEC2EnrichedRealizationSingularComparison
open DaggerNativeOriginalC2RealizationMapping
open scoped SSet.modelCategoryQuillen DaggerOriginalSimplicialActionModelCategory
universe u
namespace DaggerNativeOriginalEC2RealizationUnitComparison
noncomputable section

def unitAction (A : Action SSet.{u} C2.{u}) : A ⟶ singularAction (realizationFunctor.obj A) where
  hom := sSetTopAdj.unit.app A.V
  comm g := sSetTopAdj.unit.naturality (A.ρ g).asHom

theorem unitAction_weak (A : Action SSet.{u} C2.{u}) : WeakEquivalence (unitAction A) := by
  apply (DaggerOriginalSimplicialActionModelCategory.weakEquivalence_iff_underlying _).2
  change WeakEquivalence (sSetTopAdj.unit.app A.V)
  infer_instance

theorem unitAction_naturality {A B : Action SSet.{u} C2.{u}} (f : A ⟶ B) :
    f ≫ unitAction B = unitAction A ≫ singularActionMap (realizationFunctor.map f) := by
  apply Action.hom_ext
  exact sSetTopAdj.unit.naturality f.hom

def comparison (A : Action SSet.{u} C2.{u}) :
    enrichedMapping simplicialAction A ⟶ mappingFunctor.obj A :=
  enrichedMappingMap simplicialAction (unitAction A) ≫
    (originalEC2EnrichedSingIso (realizationFunctor.obj A)).hom

theorem comparison_weak (A : Action SSet.{u} C2.{u}) [A.V.KanComplex] :
    WeakEquivalence (comparison A) := by
  have : IsFibrant A :=
    (DaggerOriginalSimplicialActionModelCategory.isFibrant_iff_underlying A).2 inferInstance
  have : (singularAction (realizationFunctor.obj A)).V.KanComplex := by
    change (TopCat.toSSet.obj (SSet.toTop.obj A.V)).KanComplex
    infer_instance
  have : IsFibrant (singularAction (realizationFunctor.obj A)) :=
    (DaggerOriginalSimplicialActionModelCategory.isFibrant_iff_underlying _).2 inferInstance
  have : WeakEquivalence (unitAction A) := unitAction_weak A
  have : WeakEquivalence (enrichedMappingMap simplicialAction (unitAction A)) :=
    originalEC2_enrichedMapping_map_weakEquivalence (unitAction A)
  unfold comparison
  infer_instance

theorem comparison_naturality {A B : Action SSet.{u} C2.{u}} (f : A ⟶ B) :
    enrichedMappingMap simplicialAction f ≫ comparison B =
      comparison A ≫ mappingFunctor.map f := by
  have h := congrArg (enrichedMappingFunctor simplicialAction).map (unitAction_naturality f)
  have he : enrichedMappingMap simplicialAction f ≫
      enrichedMappingMap simplicialAction (unitAction B) =
    enrichedMappingMap simplicialAction (unitAction A) ≫
      enrichedMappingMap simplicialAction (singularActionMap (realizationFunctor.map f)) := by
    simpa only [CategoryTheory.Functor.map_comp] using h
  unfold comparison
  rw [← Category.assoc, he, Category.assoc]
  change enrichedMappingMap simplicialAction (unitAction A) ≫
      (originalEC2EnrichedSingMappingMap (realizationFunctor.map f) ≫
        (originalEC2EnrichedSingIso (realizationFunctor.obj B)).hom) = _
  rw [originalEC2EnrichedSingIso_naturality]
  exact (Category.assoc _ _ _).symm

end
end DaggerNativeOriginalEC2RealizationUnitComparison
