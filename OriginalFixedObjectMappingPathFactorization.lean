import OriginalSimplicialMappingPathFibrations

/-!
# Actual mapping-path weak-equivalence/fibration factorization

Every original fixed-object strict groupoid functor, ordinary or dagger,
factors through the unchanged original mapping-path pullback. The first map
is an actual Homwise weak equivalence and the second a Homwise fibration.
No model existence or extra Kan hypothesis is assumed on the original objects.
-/

set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory HomotopicalAlgebra Simplicial DaggerModels
open DaggerOriginalFixedObjectSimplicialCategories DaggerOriginalFixedObjectDaggerCategories
open DaggerOriginalFixedObjectCotensorPoints DaggerOriginalFixedObjectGroupoidInterval
open DaggerOriginalFixedObjectGroupoidClasses DaggerOriginalFixedObjectCotensorFibrations
open DaggerOriginalFixedObjectStrictPullbacks DaggerOriginalFixedObjectDaggerPullbacks
open DaggerOriginalFixedObjectPullbackFibrations DaggerOriginalSimplicialMappingPathFibrations
open DaggerOriginalFixedObjectGroupoidHomPathFactorization
open scoped SSet.modelCategoryQuillen DaggerOriginalFixedObjectGroupoidClasses
universe u
namespace DaggerOriginalFixedObjectMappingPathFactorization
noncomputable section

/-- Evaluating either actual interval endpoint is a weak equivalence for a Kan Hom. -/
theorem endpoint_weakEquivalence (X : SSet.{u}) [X.KanComplex] (v : Fin 2) :
    WeakEquivalence (pointEvaluation (intervalPoint v) X) := by
  have : WeakEquivalence (constantHom Δ[1] X) := constantHom_weakEquivalence X
  have : WeakEquivalence (constantHom Δ[1] X ≫ pointEvaluation (intervalPoint v) X) := by
    rw [constantHom_evaluation]
    infer_instance
  exact weakEquivalence_of_precomp (constantHom Δ[1] X) (pointEvaluation (intervalPoint v) X)

/-- The original interval evaluation is a trivial fibration in the entire Homwise class. -/
theorem strictEvaluation_trivialFibration {O : Type u} (C : FixedStrictGroupoids O)
    (v : Fin 2) : Fibration (strictEvaluation (intervalPoint v) C) ∧
      WeakEquivalence (strictEvaluation (intervalPoint v) C) := by
  refine ⟨(strict_fibration_iff _).2 (strictEvaluation_hom_fibration (intervalPoint v) C),
    (strict_weakEquivalence_iff _).2 ?_⟩
  intro x y
  have : (C.obj.enriched.Hom x y).KanComplex := fixedStrictHom_kan C x y
  exact endpoint_weakEquivalence (C.obj.enriched.Hom x y) v

/-- The original dagger evaluation also retains both actual Homwise model classes. -/
theorem strictDaggerEvaluation_trivialFibration {O : Type u}
    (C : FixedStrictDaggerGroupoids O) (v : Fin 2) :
    Fibration (strictDaggerEvaluation (intervalPoint v) C) ∧
      WeakEquivalence (strictDaggerEvaluation (intervalPoint v) C) := by
  refine ⟨(strictDagger_fibration_iff _).2
    (strictDaggerEvaluation_hom_fibration (intervalPoint v) C),
    (strictDagger_weakEquivalence_iff _).2 ?_⟩
  intro x y
  have : (C.obj.underlying.enriched.Hom x y).KanComplex :=
    fixedStrictHom_kan ⟨C.obj.underlying, C.property⟩ x y
  exact endpoint_weakEquivalence (C.obj.underlying.enriched.Hom x y) v

/-- The actual same-O mapping-path object of the whole original strict functor. -/
def mappingPath {O : Type u} {C D : FixedStrictGroupoids O} (F : C ⟶ D) :
    FixedStrictGroupoids O := strictPullback F (strictEvaluation (intervalPoint 0) D)

/-- The entire original constant-path inclusion. -/
def mappingInclusion {O : Type u} {C D : FixedStrictGroupoids O} (F : C ⟶ D) :
    C ⟶ mappingPath F :=
  strictLift (𝟙 C) (F ≫ strictConstant Δ[1] D) (by
    rw [Category.assoc, strictConstant_evaluation, Category.comp_id, Category.id_comp])

/-- Evaluate the other actual endpoint of the entire original path. -/
def mappingProjection {O : Type u} {C D : FixedStrictGroupoids O} (F : C ⟶ D) :
    mappingPath F ⟶ D :=
  strictSnd F (strictEvaluation (intervalPoint 0) D) ≫ strictEvaluation (intervalPoint 1) D

/-- The whole original functor is exactly the composite of these two actual factors. -/
theorem mappingInclusion_projection {O : Type u} {C D : FixedStrictGroupoids O} (F : C ⟶ D) :
    mappingInclusion F ≫ mappingProjection F = F := by
  dsimp only [mappingInclusion, mappingProjection]
  rw [← Category.assoc, strictLift_snd, Category.assoc, strictConstant_evaluation,
    Category.comp_id]

/-- The actual inclusion is a weak equivalence on each unchanged original Hom. -/
theorem mappingInclusion_weakEquivalence {O : Type u} {C D : FixedStrictGroupoids O}
    (F : C ⟶ D) : WeakEquivalence (mappingInclusion F) := by
  have : Fibration (strictEvaluation (intervalPoint 0) D) :=
    (strictEvaluation_trivialFibration D 0).1
  have : WeakEquivalence (strictEvaluation (intervalPoint 0) D) :=
    (strictEvaluation_trivialFibration D 0).2
  have hw := (strictFst_trivialFibration F (strictEvaluation (intervalPoint 0) D)).2
  apply (strict_weakEquivalence_iff _).2
  intro x y
  have : WeakEquivalence
      ((strictFst F (strictEvaluation (intervalPoint 0) D)).hom.map x y) :=
    (strict_weakEquivalence_iff _).1 hw x y
  have h := congrArg (fun k : C ⟶ C ↦ k.hom.map x y)
    (strictLift_fst (F := F) (G := strictEvaluation (intervalPoint 0) D)
      (𝟙 C) (F ≫ strictConstant Δ[1] D) (by
      rw [Category.assoc, strictConstant_evaluation, Category.comp_id, Category.id_comp]))
  change (mappingInclusion F).hom.map x y ≫
    (strictFst F (strictEvaluation (intervalPoint 0) D)).hom.map x y = 𝟙 _ at h
  have : WeakEquivalence ((mappingInclusion F).hom.map x y ≫
      (strictFst F (strictEvaluation (intervalPoint 0) D)).hom.map x y) := by
    rw [h]
    infer_instance
  exact weakEquivalence_of_postcomp ((mappingInclusion F).hom.map x y)
    ((strictFst F (strictEvaluation (intervalPoint 0) D)).hom.map x y)

/-- The actual other-endpoint projection is a fibration on every unchanged original Hom. -/
theorem mappingProjection_fibration {O : Type u} {C D : FixedStrictGroupoids O}
    (F : C ⟶ D) : Fibration (mappingProjection F) := by
  apply (strict_fibration_iff _).2
  intro x y
  have : (C.obj.enriched.Hom x y).KanComplex := fixedStrictHom_kan C x y
  have : (D.obj.enriched.Hom x y).KanComplex := fixedStrictHom_kan D x y
  exact mappingEndpoint_fibration (F.hom.map x y)

/-- The actual same-O mapping-path object retains the whole original dagger. -/
def daggerMappingPath {O : Type u} {C D : FixedStrictDaggerGroupoids O} (F : C ⟶ D) :
    FixedStrictDaggerGroupoids O :=
  strictDaggerPullback F (strictDaggerEvaluation (intervalPoint 0) D)

/-- The whole original dagger constant-path inclusion. -/
def daggerMappingInclusion {O : Type u} {C D : FixedStrictDaggerGroupoids O} (F : C ⟶ D) :
    C ⟶ daggerMappingPath F :=
  strictDaggerLift (𝟙 C) (F ≫ strictDaggerConstant Δ[1] D) (by
    rw [Category.assoc, strictDaggerConstant_evaluation, Category.comp_id, Category.id_comp])

/-- The other original dagger endpoint of the entire original mapping path. -/
def daggerMappingProjection {O : Type u} {C D : FixedStrictDaggerGroupoids O} (F : C ⟶ D) :
    daggerMappingPath F ⟶ D :=
  strictDaggerSnd F (strictDaggerEvaluation (intervalPoint 0) D) ≫
    strictDaggerEvaluation (intervalPoint 1) D

/-- Exact whole-functor factorization in the unchanged original strict dagger category. -/
theorem daggerMappingInclusion_projection {O : Type u} {C D : FixedStrictDaggerGroupoids O}
    (F : C ⟶ D) : daggerMappingInclusion F ≫ daggerMappingProjection F = F := by
  dsimp only [daggerMappingInclusion, daggerMappingProjection]
  rw [← Category.assoc, strictDaggerLift_snd, Category.assoc, strictDaggerConstant_evaluation,
    Category.comp_id]

/-- The actual whole dagger inclusion is a weak equivalence on every unchanged Hom. -/
theorem daggerMappingInclusion_weakEquivalence {O : Type u} {C D : FixedStrictDaggerGroupoids O}
    (F : C ⟶ D) : WeakEquivalence (daggerMappingInclusion F) := by
  have : Fibration (strictDaggerEvaluation (intervalPoint 0) D) :=
    (strictDaggerEvaluation_trivialFibration D 0).1
  have : WeakEquivalence (strictDaggerEvaluation (intervalPoint 0) D) :=
    (strictDaggerEvaluation_trivialFibration D 0).2
  have hw := (strictDaggerFst_trivialFibration F (strictDaggerEvaluation (intervalPoint 0) D)).2
  apply (strictDagger_weakEquivalence_iff _).2
  intro x y
  have : WeakEquivalence
      ((strictDaggerFst F (strictDaggerEvaluation (intervalPoint 0) D)).hom.underlying.map x y) :=
    (strictDagger_weakEquivalence_iff _).1 hw x y
  have h := congrArg (fun k : C ⟶ C ↦ k.hom.underlying.map x y)
    (strictDaggerLift_fst (F := F) (G := strictDaggerEvaluation (intervalPoint 0) D)
      (𝟙 C) (F ≫ strictDaggerConstant Δ[1] D) (by
      rw [Category.assoc, strictDaggerConstant_evaluation, Category.comp_id, Category.id_comp]))
  change (daggerMappingInclusion F).hom.underlying.map x y ≫
    (strictDaggerFst F (strictDaggerEvaluation (intervalPoint 0) D)).hom.underlying.map x y =
      𝟙 _ at h
  have : WeakEquivalence ((daggerMappingInclusion F).hom.underlying.map x y ≫
      (strictDaggerFst F (strictDaggerEvaluation (intervalPoint 0) D)).hom.underlying.map x y) := by
    rw [h]
    infer_instance
  exact weakEquivalence_of_postcomp ((daggerMappingInclusion F).hom.underlying.map x y)
    ((strictDaggerFst F (strictDaggerEvaluation (intervalPoint 0) D)).hom.underlying.map x y)

/-- The actual whole dagger endpoint projection is a fibration on every unchanged Hom. -/
theorem daggerMappingProjection_fibration {O : Type u} {C D : FixedStrictDaggerGroupoids O}
    (F : C ⟶ D) : Fibration (daggerMappingProjection F) := by
  apply (strictDagger_fibration_iff _).2
  intro x y
  have : (C.obj.underlying.enriched.Hom x y).KanComplex :=
    fixedStrictHom_kan ⟨C.obj.underlying, C.property⟩ x y
  have : (D.obj.underlying.enriched.Hom x y).KanComplex :=
    fixedStrictHom_kan ⟨D.obj.underlying, D.property⟩ x y
  exact mappingEndpoint_fibration (F.hom.underlying.map x y)

end
end DaggerOriginalFixedObjectMappingPathFactorization
