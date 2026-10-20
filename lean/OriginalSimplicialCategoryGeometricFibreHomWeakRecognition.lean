import NativeSSetCoproductComponentWeakEquivalence
import OriginalSimplicialCategoryWholeBarGeometricFibreNaturality
import OriginalSimplicialCategoryWholeBarFibreLocalization
import OriginalCompletionWeakNecessity

/-!
# Exact weak-equivalence recognition from actual geometric strict fibres

Every original enriched functor acts on the full original Hom coproduct and
on the actual point fibre of the realized original bar projection. The proved
homeomorphisms identify the two weak-equivalence assertions. For the actual
localization unit, weakness of its geometric fibre map implies weakness of
each original localization Hom map, with no original Kan/cofibrancy premise.
The remaining quasifibration and homotopy-fibre comparisons are not assumed.
-/
set_option autoImplicit false
open CategoryTheory Limits Simplicial DaggerModels HomotopicalAlgebra
open DaggerNativeSSetCoproductComponentWeakEquivalence
open DaggerOriginalSimplicialCategoryWholeBarFibreIso
open DaggerOriginalSimplicialCategoryWholeBarFibreFunctor
open DaggerOriginalSimplicialCategoryWholeBarGeometricStrictFibre
open DaggerOriginalSimplicialCategoryWholeBarGeometricFibreNaturality
open DaggerOriginalSimplicialCategoryWholeBarFibreLocalization
open DaggerOriginalSimplicialGroupoidCompletion
open scoped TopCat.modelCategory SSet.modelCategoryQuillen
universe u
namespace DaggerOriginalSimplicialCategoryGeometricFibreHomWeakRecognition
noncomputable section

/-- The actual geometric strict-fibre homeomorphism as a native TopCat isomorphism. -/
def geometricFibreIso (C : SimplicialCat.{u, u}) (x : C.Obj) :
    SSet.toTop.obj (originalHomSum C x) ≅ TopCat.of (geometricWholeBarFibre C x) :=
  TopCat.isoOfHomeo (wholeBarHomGeometricFibreHomeomorph C x)

/-- The native isomorphism keeps the exact original realized Hom map and geometric fibre map. -/
theorem geometricFibreIso_natural {C D : SimplicialCat.{u, u}} (F : C ⟶ D) (x : C.Obj) :
    (geometricFibreIso C x).hom ≫ geometricWholeBarFibreMap F x =
      SSet.toTop.map (originalHomSumMap F x) ≫ (geometricFibreIso D (F.obj x)).hom := by
  ext a
  exact congrArg Subtype.val (wholeBarHomGeometricFibreHomeomorph_natural F x a)

/-- The actual full Hom-coproduct map is weak exactly when its actual geometric fibre map is. -/
theorem originalHomSumMap_weakEquivalence_iff_geometricFibreMap
    {C D : SimplicialCat.{u, u}} (F : C ⟶ D) (x : C.Obj) :
    WeakEquivalence (originalHomSumMap F x) ↔
      WeakEquivalence (geometricWholeBarFibreMap F x) := by
  rw [SSet.modelCategoryQuillen.weakEquivalence_iff]
  constructor
  · intro h
    have := h
    have : WeakEquivalence
        (SSet.toTop.map (originalHomSumMap F x) ≫ (geometricFibreIso D (F.obj x)).hom) :=
      inferInstance
    have : WeakEquivalence ((geometricFibreIso C x).hom ≫ geometricWholeBarFibreMap F x) := by
      rw [geometricFibreIso_natural]
      infer_instance
    exact weakEquivalence_of_precomp (geometricFibreIso C x).hom (geometricWholeBarFibreMap F x)
  · intro h
    have := h
    have : WeakEquivalence ((geometricFibreIso C x).hom ≫ geometricWholeBarFibreMap F x) :=
      inferInstance
    have : WeakEquivalence
        (SSet.toTop.map (originalHomSumMap F x) ≫ (geometricFibreIso D (F.obj x)).hom) := by
      rw [← geometricFibreIso_natural]
      infer_instance
    exact weakEquivalence_of_postcomp (SSet.toTop.map (originalHomSumMap F x))
      (geometricFibreIso D (F.obj x)).hom

/-- Weakness of the actual unit's geometric fibre map implies every actual Hom localization weak. -/
theorem localizationHom_weakEquivalence_of_geometricFibreMap (C : SimplicialCat.{u, u})
    (x : C.Obj) (h : WeakEquivalence (geometricWholeBarFibreMap (localization C) x))
    (y : C.Obj) : WeakEquivalence (localizationHom C x y) := by
  have hsum := (originalHomSumMap_weakEquivalence_iff_geometricFibreMap
    (localization C) x).2 h
  rw [originalHomSumMap_localization] at hsum
  exact coproductComponent_weakEquivalence (localizationHom C x) hsum y

/-- Weakness on every actual geometric unit fibre forces the unchanged original pi0 groupoid. -/
theorem geometricFibreMapsWeak_implies_actualPiZeroGroupoid (C : SimplicialCat.{u, u})
    (h : ∀ x : C.Obj, WeakEquivalence (geometricWholeBarFibreMap (localization C) x)) :
    DaggerOriginalAmbientDaggerPiZeroGroupoid.HasActualComponentGroupoid C := by
  apply DaggerOriginalCompletionWeakNecessity.localizationWeak_implies_actualPiZeroGroupoid
  intro x y
  exact localizationHom_weakEquivalence_of_geometricFibreMap C x (h x) y

end
end DaggerOriginalSimplicialCategoryGeometricFibreHomWeakRecognition
