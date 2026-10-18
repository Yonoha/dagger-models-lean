import OriginalSimplicialCategoryWholeBarFibreFunctor

/-!
# The actual localization on the whole original strict Hom fibre

Specialize full original functor naturality to the actual original groupoid
completion unit. Its original object map is the identity, so the whole Hom map
is literally the native coproduct of all original localization Hom maps.
No weak equivalence of this strict-fibre map is assumed or asserted.
-/
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Simplicial DaggerModels
open DaggerOriginalSimplicialGroupoidCompletion
open DaggerOriginalSimplicialCategoryBarConstruction
open DaggerOriginalSimplicialCategoryWholeBarLocalization
open DaggerOriginalSimplicialCategoryWholeBarFibreDegree
open DaggerOriginalSimplicialCategoryWholeBarFibreIso
open DaggerOriginalSimplicialCategoryWholeBarFibreFunctor
universe u
namespace DaggerOriginalSimplicialCategoryWholeBarFibreLocalization
noncomputable section

/-- The actual whole original localization Hom map includes every original endpoint. -/
def wholeHomLocalization (C : SimplicialCat.{u, u}) (x : C.Obj) :
    originalHomSum C x ⟶ originalHomSum (completion C) x :=
  Limits.Sigma.map (localizationHom C x)

/-- Reindexing by the actual unit is the native coproduct of its unchanged original Hom maps. -/
theorem originalHomSumMap_localization (C : SimplicialCat.{u, u}) (x : C.Obj) :
    originalHomSumMap (localization C) x = wholeHomLocalization C x := by
  change Limits.Sigma.map' id (localizationHom C x) = Limits.Sigma.map (localizationHom C x)
  exact Sigma.map'_id (localizationHom C x)

/-- The actual whole Hom localization commutes with the actual whole bar inclusions. -/
theorem wholeHomLocalization_inclusion (C : SimplicialCat.{u, u}) (x : C.Obj) :
    wholeHomLocalization C x ≫ wholeBarHomInclusion (completion C) x =
      wholeBarHomInclusion C x ≫ wholeBarLocalization C := by
  rw [← originalHomSumMap_localization]
  exact wholeBarHomInclusion_natural (localization C) x

/-- The actual whole strict-fibre map is exactly the actual original Hom localization sum. -/
theorem wholeHomLocalization_fibreIso (C : SimplicialCat.{u, u}) (x : C.Obj) :
    wholeHomLocalization C x ≫ (wholeBarHomFibreIso (completion C) x).hom =
      (wholeBarHomFibreIso C x).hom ≫ wholeBarFibreMap (localization C) x := by
  rw [← originalHomSumMap_localization]
  exact wholeBarHomFibreIso_natural (localization C) x

/-- The full original Hom localization and bar localization form the actual comparison square. -/
theorem wholeHomLocalization_square (C : SimplicialCat.{u, u}) (x : C.Obj) :
    CommSq (wholeHomLocalization C x) (wholeBarHomInclusion C x)
      (wholeBarHomInclusion (completion C) x) (wholeBarLocalization C) :=
  ⟨wholeHomLocalization_inclusion C x⟩

end
end DaggerOriginalSimplicialCategoryWholeBarFibreLocalization
