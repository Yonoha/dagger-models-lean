import OriginalFixedObjectDaggerCotensorRepresentation
import OriginalFixedObjectCompletionMappingComparison
import TopCatModelCategory.SSet.StandardSimplex

/-!
# Original completion comparison on the full Mathlib enriched mapping objects

The all-parameter cotensor equivalence and Yoneda identify the cotensor-presented
mapping simplicial sets with the actual native enrichment in every dimension.
Transport the original completion comparison along these complete isomorphisms.
Both ordinary and dagger comparisons retain precisely the original fixed objects.
This identifies enriched mapping objects, without claiming derived model mappings.
-/

set_option autoImplicit false
open CategoryTheory MonoidalCategory Opposite Simplicial DaggerModels
open DaggerOriginalFixedObjectSimplicialCategories DaggerOriginalFixedObjectDaggerCategories
open DaggerOriginalFixedObjectGroupoidCompletionAdjunction DaggerOriginalFixedObjectCotensors
open DaggerOriginalFixedObjectStrictGroupoidCotensors
universe u

namespace DaggerOriginalFixedObjectNativeMappingComparison

noncomputable section

/-- All simplices of the actual ordinary mapping object are original cotensor functors. -/
def simplexEquiv {O : Type u} (C D : FixedSimplicialCategory O) (n : SimplexCategoryᵒᵖ) :
    (DaggerOriginalFixedObjectSimplicialEnrichment.mapping C D).obj n ≃
      (C ⟶ cotensor (SSet.stdSimplex.obj n.unop) D) :=
  SSet.yonedaEquiv.symm.trans
    (DaggerOriginalFixedObjectCotensorRepresentation.cotensorHomEquiv C D _)

/-- The entire native ordinary mapping object is the same cotensor-presented simplicial set. -/
def mappingIso {O : Type u} (C D : FixedSimplicialCategory O) :
    DaggerOriginalFixedObjectSimplicialEnrichment.mapping C D ≅
      DaggerOriginalFixedObjectCompletionMappingComparison.mapping C D := by
  refine NatIso.ofComponents (fun n ↦ (simplexEquiv C D n).toIso) ?_
  intro n m i
  funext f
  change DaggerOriginalFixedObjectCotensorRepresentation.cotensorHomEquiv C D _
    (SSet.yonedaEquiv.symm
      ((DaggerOriginalFixedObjectSimplicialEnrichment.mapping C D).map i f)) =
      DaggerOriginalFixedObjectCotensorRepresentation.cotensorHomEquiv C D _
        (SSet.yonedaEquiv.symm f) ≫ cotensorPre (SSet.stdSimplex.map i.unop) D
  have h := SSet.yonedaEquiv_symm_map i.unop f
  simp only [Quiver.Hom.op_unop] at h
  rw [h]
  exact DaggerOriginalFixedObjectCotensorRepresentation.cotensorHomEquiv_parameter C D _ _

/-- All simplices of the actual dagger mapping object retain the original dagger functors. -/
def daggerSimplexEquiv {O : Type u} (C D : FixedDaggerCategory O) (n : SimplexCategoryᵒᵖ) :
    (DaggerOriginalFixedObjectDaggerSimplicialEnrichment.mapping C D).obj n ≃
      (C ⟶ daggerCotensor (SSet.stdSimplex.obj n.unop) D) :=
  SSet.yonedaEquiv.symm.trans
    (DaggerOriginalFixedObjectDaggerCotensorRepresentation.cotensorHomEquiv C D _)

/-- The whole native dagger mapping object includes every original simplex operator. -/
def daggerMappingIso {O : Type u} (C D : FixedDaggerCategory O) :
    DaggerOriginalFixedObjectDaggerSimplicialEnrichment.mapping C D ≅
      DaggerOriginalFixedObjectCompletionMappingComparison.daggerMapping C D := by
  refine NatIso.ofComponents (fun n ↦ (daggerSimplexEquiv C D n).toIso) ?_
  intro n m i
  funext f
  change DaggerOriginalFixedObjectDaggerCotensorRepresentation.cotensorHomEquiv C D _
    (SSet.yonedaEquiv.symm
      ((DaggerOriginalFixedObjectDaggerSimplicialEnrichment.mapping C D).map i f)) =
      DaggerOriginalFixedObjectDaggerCotensorRepresentation.cotensorHomEquiv C D _
        (SSet.yonedaEquiv.symm f) ≫ daggerCotensorPre (SSet.stdSimplex.map i.unop) D
  have h := SSet.yonedaEquiv_symm_map i.unop f
  simp only [Quiver.Hom.op_unop] at h
  rw [h]
  exact DaggerOriginalFixedObjectDaggerCotensorRepresentation.cotensorHomEquiv_parameter C D _ _

/-- Full subcategory arrows into the strict cotensor are exactly the original arrows. -/
def strictSimplexEquiv {O : Type u} (C D : FixedStrictGroupoids O)
    (n : SimplexCategoryᵒᵖ) :
    (C ⟶ strictCotensor (SSet.stdSimplex.obj n.unop) D) ≃
      (C.obj ⟶ cotensor (SSet.stdSimplex.obj n.unop) D.obj) where
  toFun F := F.hom
  invFun F := ObjectProperty.homMk F
  left_inv F := by cases F; rfl
  right_inv _ := rfl

/-- The strict ordinary mapping presentation has the unchanged original full Hom sets. -/
def strictMappingIso {O : Type u} (C D : FixedStrictGroupoids O) :
    DaggerOriginalFixedObjectCompletionMappingComparison.strictMapping C D ≅
      DaggerOriginalFixedObjectCompletionMappingComparison.mapping C.obj D.obj := by
  refine NatIso.ofComponents (fun n ↦ (strictSimplexEquiv C D n).toIso) ?_
  intro n m i
  funext F
  rfl

/-- Strict dagger cotensor arrows retain all original fixed-object dagger functors. -/
def strictDaggerSimplexEquiv {O : Type u} (C D : FixedStrictDaggerGroupoids O)
    (n : SimplexCategoryᵒᵖ) :
    (C ⟶ strictDaggerCotensor (SSet.stdSimplex.obj n.unop) D) ≃
      (C.obj ⟶ daggerCotensor (SSet.stdSimplex.obj n.unop) D.obj) where
  toFun F := F.hom
  invFun F := ObjectProperty.homMk F
  left_inv F := by cases F; rfl
  right_inv _ := rfl

/-- The strict dagger mapping presentation retains the same Hom sets and operators. -/
def strictDaggerMappingIso {O : Type u} (C D : FixedStrictDaggerGroupoids O) :
    DaggerOriginalFixedObjectCompletionMappingComparison.strictDaggerMapping C D ≅
      DaggerOriginalFixedObjectCompletionMappingComparison.daggerMapping C.obj D.obj := by
  refine NatIso.ofComponents (fun n ↦ (strictDaggerSimplexEquiv C D n).toIso) ?_
  intro n m i
  funext F
  rfl

/-- Original ordinary completion gives an isomorphism of the actual Mathlib enriched Hom. -/
def completionMappingIso {O : Type u} (C : FixedSimplicialCategory O)
    (D : FixedStrictGroupoids O) :
    (((fixedCompletion O).obj C) ⟶[SSet.{u}] D) ≅ (C ⟶[SSet.{u}] D.obj) :=
  mappingIso _ _ ≪≫ (strictMappingIso _ _).symm ≪≫
    DaggerOriginalFixedObjectCompletionMappingComparison.completionMappingIso C D ≪≫
      (mappingIso C D.obj).symm

/-- Original dagger completion gives an isomorphism of full Mathlib dagger enriched Hom. -/
def daggerCompletionMappingIso {O : Type u} (C : FixedDaggerCategory O)
    (D : FixedStrictDaggerGroupoids O) :
    (((fixedDaggerCompletion O).obj C) ⟶[SSet.{u}] D) ≅ (C ⟶[SSet.{u}] D.obj) :=
  daggerMappingIso _ _ ≪≫ (strictDaggerMappingIso _ _).symm ≪≫
    DaggerOriginalFixedObjectCompletionMappingComparison.daggerCompletionMappingIso C D ≪≫
      (daggerMappingIso C D.obj).symm

end

end DaggerOriginalFixedObjectNativeMappingComparison
