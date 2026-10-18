import OriginalFixedObjectStrictDaggerGenerators
import FixedCategoryHomLimits

/-!
# Filtered colimits preserve the exact original degree invertibility condition

The legacy Hom evaluations preserve filtered colimits. Every simplex of the ambient colimit
therefore comes from an original diagram stage, where it is invertible. The actual degree
functor carries that inverse to the colimit. No strict model structure is assumed.
-/

set_option autoImplicit false
open CategoryTheory Limits DaggerModels
open DaggerOriginalFixedObjectSimplicialCategories DaggerOriginalFixedObjectDaggerCategories
open DaggerOriginalFixedObjectLegacyDaggerEquivalence
open DaggerOriginalFixedObjectGroupoidCompletionAdjunction
open DaggerOriginalSimplicialDegreeCategory
universe u
namespace DaggerOriginalFixedObjectDaggerFilteredColimits
noncomputable section

/-- Evaluate exactly the original fixed dagger Hom, using the verified legacy presentation. -/
def ambientHomEvaluation (O : Type u) (x y : O) : FixedDaggerCategory O ⥤ SSet.{u} :=
  (legacyDaggerEquivalence O).functor ⋙ DaggerFixedCategoryHomLimits.homEval O x y

/-- Reuse native preservation of filtered colimits by the original legacy Hom evaluation. -/
instance ambientHomPreservesFiltered (O : Type u) (x y : O) (J : Type u)
    [SmallCategory J] [IsFiltered J] : PreservesColimitsOfShape J (ambientHomEvaluation O x y)
    := by
  letI := DaggerFixedCategoryHomLimits.homEvalPreservesFilteredColimits O x y J
  unfold ambientHomEvaluation
  infer_instance

/-- The ambient colimit of original strict dagger groupoids is still degreewise a groupoid. -/
theorem ambientFilteredColimit_isStrict {O J : Type u} [SmallCategory J] [IsFiltered J]
    (K : J ⥤ FixedStrictDaggerGroupoids O) :
    IsStrictFixedDagger (colimit (K ⋙ fixedDaggerInclusion O)) := by
  intro n x y f
  let F := K ⋙ fixedDaggerInclusion O
  let E := ambientHomEvaluation O x y ⋙
    (CategoryTheory.evaluation SimplexCategoryᵒᵖ (Type u)).obj n
  have hc := isColimitOfPreserves E (colimit.isColimit F)
  obtain ⟨j, g, hg⟩ := Types.jointly_surjective_of_isColimit hc f
  change ((colimit.ι F j).underlying.map x y).app n g = f at hg
  haveI : @IsIso (degreeObjects (original O (K.obj j).obj.underlying) n)
      (degreeCategory (original O (K.obj j).obj.underlying) n) x y g :=
    (K.obj j).property n x y g
  have hm : IsIso ((degreeFunctor (originalHom (colimit.ι F j).underlying) n).map g) :=
    inferInstance
  have he : (degreeFunctor (originalHom (colimit.ι F j).underlying) n).map g = f := hg
  exact he ▸ hm

/-- The exact ambient colimit cocone, regarded as a cocone in the original strict subcategory. -/
def filteredCocone {O J : Type u} [SmallCategory J] [IsFiltered J]
    (K : J ⥤ FixedStrictDaggerGroupoids O) : Cocone K where
  pt := ⟨colimit (K ⋙ fixedDaggerInclusion O), ambientFilteredColimit_isStrict K⟩
  ι :=
    { app j := ObjectProperty.homMk (colimit.ι (K ⋙ fixedDaggerInclusion O) j)
      naturality i j f := by
        apply ObjectProperty.hom_ext _
        simpa only [Functor.const_obj_map, Category.comp_id] using
          colimit.w (K ⋙ fixedDaggerInclusion O) f }

/-- The mapped strict cocone is exactly the native ambient colimit cocone. -/
def mappedFilteredIsColimit {O J : Type u} [SmallCategory J] [IsFiltered J]
    (K : J ⥤ FixedStrictDaggerGroupoids O) :
    IsColimit ((fixedDaggerInclusion O).mapCocone (filteredCocone K)) :=
  colimit.isColimit (K ⋙ fixedDaggerInclusion O)

/-- Full-subcategory reflection proves the complete strict colimit universal property. -/
def filteredIsColimit {O J : Type u} [SmallCategory J] [IsFiltered J]
    (K : J ⥤ FixedStrictDaggerGroupoids O) : IsColimit (filteredCocone K) :=
  ObjectProperty.ιReflectsIsColimit (IsStrictFixedDagger (O := O)) (mappedFilteredIsColimit K)

end
end DaggerOriginalFixedObjectDaggerFilteredColimits
