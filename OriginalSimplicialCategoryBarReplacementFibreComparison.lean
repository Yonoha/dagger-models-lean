import NativeSSetFibrationSquareFibreWeak
import OriginalSimplicialCategoryGeometricFibreHomWeakRecognition
import OriginalSimplicialCategoryWholeBarLocalization

/-!
# Exact original bar projection replacement and the remaining strict-fibre comparison

Factor the actual original whole-bar projection as a trivial cofibration
followed by a Kan fibration over the unchanged actual diagonal nerve.
The comparison starts at the full original Hom coproduct. Every original
enriched functor has a chosen actual lift between replacements, and the
comparison square keeps its original Hom maps and object reindexing.
The weak-equivalence criterion explicitly retains the unproved comparison
hypotheses; it does not assume the original bar projection is a fibration.
-/
set_option autoImplicit false
open CategoryTheory Limits HomotopicalAlgebra Simplicial DaggerModels
open DaggerOriginalSimplicialCategoryDiagonalNerve
open DaggerOriginalSimplicialCategoryBarConstruction
open DaggerOriginalSimplicialCategoryBarFunctor
open DaggerOriginalSimplicialCategoryBarFibre
open DaggerOriginalSimplicialCategoryBarFibreFunctor
open DaggerOriginalSimplicialCategoryWholeBarFibreIso
open DaggerOriginalSimplicialCategoryWholeBarFibrePullback
open DaggerOriginalSimplicialCategoryWholeBarFibreFunctor
open DaggerOriginalSimplicialCategoryWholeBarFibreLocalization
open DaggerOriginalSimplicialCategoryWholeBarLocalization
open DaggerOriginalSimplicialGroupoidCompletion
open DaggerNativeSSetFibrationSquareFibreWeak
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerOriginalSimplicialCategoryBarReplacementFibreComparison
noncomputable section

/-- Replace the actual original bar projection over the unchanged actual diagonal nerve. -/
def projectionReplacement (C : SimplicialCat.{u, u}) :
    MorphismProperty.MapFactorizationData (trivialCofibrations SSet)
      (fibrations SSet) (barProjection C) :=
  MorphismProperty.factorizationData (trivialCofibrations SSet) (fibrations SSet) _

/-- The actual original comparison into the replacement total object is weak. -/
theorem projectionReplacement_i_weak (C : SimplicialCat.{u, u}) :
    WeakEquivalence (projectionReplacement C).i :=
  ((mem_trivialCofibrations_iff _).1 (projectionReplacement C).hi).2

/-- The actual replacement projection to the original diagonal nerve is a Kan fibration. -/
theorem projectionReplacement_p_fibration (C : SimplicialCat.{u, u}) :
    Fibration (projectionReplacement C).p :=
  (fibration_iff _).2 (projectionReplacement C).hp

/-- The actual fibre of the replaced projection at the unchanged original source vertex. -/
def replacementFibre (C : SimplicialCat.{u, u}) (x : C.Obj) : SSet.{u} :=
  pullback (projectionReplacement C).p (sourceVertexMap C x)

/-- Compare the full original Hom coproduct with the fibre of the replaced projection. -/
def strictFibreComparison (C : SimplicialCat.{u, u}) (x : C.Obj) :
    originalHomSum C x ⟶ replacementFibre C x :=
  pullback.lift (wholeBarHomInclusion C x ≫ (projectionReplacement C).i)
    (SSet.stdSimplex.isTerminalObj₀.from (originalHomSum C x)) (by
      rw [Category.assoc, (projectionReplacement C).fac]
      exact (wholeBarHomIsPullback C x).w)

/-- The actual original functor square admits the replacement lifting problem. -/
def replacementSquare {C D : SimplicialCat.{u, u}} (F : C ⟶ D) :
    CommSq (barMap F ≫ (projectionReplacement D).i) (projectionReplacement C).i
      (projectionReplacement D).p ((projectionReplacement C).p ≫ diagonalNerveFunctor.map F) :=
  ⟨by
    rw [Category.assoc, (projectionReplacement D).fac, barProjection_natural,
      ← Category.assoc, (projectionReplacement C).fac]⟩

/-- Choose an actual lift extending the original whole-bar map over its original nerve map. -/
def replacementMap {C D : SimplicialCat.{u, u}} (F : C ⟶ D) :
    (projectionReplacement C).Z ⟶ (projectionReplacement D).Z := by
  have : Cofibration (projectionReplacement C).i :=
    ((mem_trivialCofibrations_iff _).1 (projectionReplacement C).hi).1
  have := projectionReplacement_i_weak C
  have := projectionReplacement_p_fibration D
  exact (replacementSquare F).lift

/-- The chosen lift extends the actual original bar map exactly. -/
theorem replacementMap_i {C D : SimplicialCat.{u, u}} (F : C ⟶ D) :
    (projectionReplacement C).i ≫ replacementMap F =
      barMap F ≫ (projectionReplacement D).i := by
  unfold replacementMap
  exact CommSq.fac_left _

/-- The chosen lift lies over the actual original diagonal nerve map exactly. -/
theorem replacementMap_p {C D : SimplicialCat.{u, u}} (F : C ⟶ D) :
    replacementMap F ≫ (projectionReplacement D).p =
      (projectionReplacement C).p ≫ diagonalNerveFunctor.map F := by
  unfold replacementMap
  exact CommSq.fac_right _

/-- Weakness of the original whole-bar map implies weakness of the chosen replacement lift. -/
theorem replacementMap_weak {C D : SimplicialCat.{u, u}} (F : C ⟶ D)
    (h : WeakEquivalence (barMap F)) : WeakEquivalence (replacementMap F) := by
  have := h
  have := projectionReplacement_i_weak C
  have := projectionReplacement_i_weak D
  exact weakEquivalence_of_precomp_of_fac (replacementMap_i F)

/-- The actual replacement fibre map retains the original source vertex and nerve map. -/
def replacementFibreMap {C D : SimplicialCat.{u, u}} (F : C ⟶ D) (x : C.Obj) :
    replacementFibre C x ⟶ replacementFibre D (F.obj x) :=
  fibreMap (projectionReplacement C).p (projectionReplacement D).p
    (replacementMap F) (diagonalNerveFunctor.map F) (replacementMap_p F).symm
    (sourceVertexMap C x) (sourceVertexMap D (F.obj x)) (sourceVertexMap_natural F x)

/-- The comparison square keeps every actual original Hom map and endpoint reindexing. -/
theorem strictFibreComparison_natural {C D : SimplicialCat.{u, u}} (F : C ⟶ D)
    (x : C.Obj) :
    strictFibreComparison C x ≫ replacementFibreMap F x =
      originalHomSumMap F x ≫ strictFibreComparison D (F.obj x) := by
  apply pullback.hom_ext
  · simp only [replacementFibreMap, Category.assoc, fibreMap_fst, strictFibreComparison,
      pullback.lift_fst]
    rw [← Category.assoc, pullback.lift_fst, Category.assoc, replacementMap_i]
    rw [← Category.assoc, ← wholeBarHomInclusion_natural, Category.assoc]
  · apply SSet.stdSimplex.isTerminalObj₀.hom_ext

/-- Weak original total and nerve maps give a weak actual replacement fibre map. -/
theorem replacementFibreMap_weak {C D : SimplicialCat.{u, u}} (F : C ⟶ D) (x : C.Obj)
    (hbar : WeakEquivalence (barMap F))
    (hnerve : WeakEquivalence (diagonalNerveFunctor.map F)) :
    WeakEquivalence (replacementFibreMap F x) := by
  have := projectionReplacement_p_fibration C
  have := projectionReplacement_p_fibration D
  have := replacementMap_weak F hbar
  have := hnerve
  exact fibreMap_weakEquivalence _ _ _ _ _ _ _ _

/-- The exact remaining comparison assumptions transfer replacement-fibre weakness to Hom sums. -/
theorem originalHomSumMap_weak_of_comparisons {C D : SimplicialCat.{u, u}}
    (F : C ⟶ D) (x : C.Obj) (hbar : WeakEquivalence (barMap F))
    (hnerve : WeakEquivalence (diagonalNerveFunctor.map F))
    (hC : WeakEquivalence (strictFibreComparison C x))
    (hD : WeakEquivalence (strictFibreComparison D (F.obj x))) :
    WeakEquivalence (originalHomSumMap F x) := by
  have := hC
  have := hD
  have := replacementFibreMap_weak F x hbar hnerve
  exact weakEquivalence_of_postcomp_of_fac (strictFibreComparison_natural F x).symm

/-- For the actual unit, diagonal weakness and the exact fibre comparisons imply each Hom weak. -/
theorem localizationHom_weak_of_diagonal_and_comparisons (C : SimplicialCat.{u, u})
    (x : C.Obj) (hnerve : WeakEquivalence (diagonalLocalization C))
    (hC : WeakEquivalence (strictFibreComparison C x))
    (hD : WeakEquivalence (strictFibreComparison (completion C) x)) (y : C.Obj) :
    WeakEquivalence (localizationHom C x y) := by
  have hsum := originalHomSumMap_weak_of_comparisons (localization C) x
    (wholeBarLocalization_weakEquivalence C) hnerve hC hD
  rw [originalHomSumMap_localization] at hsum
  exact DaggerNativeSSetCoproductComponentWeakEquivalence.coproductComponent_weakEquivalence
    (localizationHom C x) hsum y

end
end DaggerOriginalSimplicialCategoryBarReplacementFibreComparison
