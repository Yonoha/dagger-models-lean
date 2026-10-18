import NativeOriginalEC2PathActionExistence
import NativeOriginalSigmaRightLeftReversal
import NativeOriginalRealSigmaUnitaryComponents
import OriginalStrictDaggerGroupoidDerivedMapping

/-! Existence of exact original strict Hom EC2 maps detects EXACT ORIGINAL unitary components. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial HomotopicalAlgebra DaggerModels OrdinaryRigidification
open DaggerOriginalSimplicialGroupoidCompletionUniversal
open DaggerOriginalStrictDaggerGroupoidMappingAction
open DaggerOriginalStrictDaggerGroupoidDerivedMapping
open DaggerOriginalStrictSimplicialGroupoidMappingKan DaggerOriginalStrictPathFiberVertices
open DaggerNativeOriginalC2RealizationMapping DaggerNativeOriginalC2QSingularSpan
open DaggerNativeOriginalSigmaRightConeHomIso DaggerNativeOriginalSigmaRightLeftReversal
open DaggerNativeOriginalRealSigmaAnchors DaggerNativeOriginalSigmaLeftPathAction
open DaggerNativeOriginalActionCanonicalConstants DaggerNativeOriginalActionCanonicalRestriction
open DaggerNativeOriginalRealSigmaUnitaryComponents DaggerOriginalFullVertexSubcomplex
open DaggerOriginalUnitaryCoreConstruction DaggerOriginalUnitaryCoreCanonicalVertices
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeOriginalStrictHomUnitaryExistence
noncomputable section

variable (C : DaggerSimplicialCat.{u, u}) (hC : IsStrictGroupoid C.toSimplicialCat)
variable (x y : Labels C)

theorem derived_vertices_iff_realized_hom :
    Nonempty ((strictDerivedMapping C hC (label C x) (label C y)) _⦋0⦌) ↔
      Nonempty ((mappingFunctor.obj (homAction C hC x y)) _⦋0⦌) := by
  have : (homAction C hC x y).V.KanComplex :=
    strictHom_kan C.toSimplicialCat hC (label C x) (label C y)
  have : (strictDerivedMapping C hC (label C x) (label C y)).KanComplex :=
    strictDerivedMapping_kan C hC (label C x) (label C y)
  have : WeakEquivalence
      (DaggerNativeOriginalEC2RealizationUnitComparison.comparison (homAction C hC x y)) :=
    DaggerNativeOriginalEC2RealizationUnitComparison.comparison_weak _
  exact vertices_nonempty_iff_of_weakEquivalence
    (DaggerNativeOriginalEC2RealizationUnitComparison.comparison (homAction C hC x y))

theorem realized_hom_vertices_iff_canonical :
    Nonempty ((mappingFunctor.obj (homAction C hC x y)) _⦋0⦌) ↔
      SSet.π₀.mk (canonicalZero (node0 C hC) x (fixed0 C hC x)) =
        SSet.π₀.mk (canonicalZero (node0 C hC) y (fixed0 C hC y)) := by
  have h := both_realized_weak C hC x y
  have : WeakEquivalence (realizedConstants (homAction C hC x y)) := h.1
  have : WeakEquivalence (rightConeToMixed C hC x y) := h.2
  have : WeakEquivalence (rightToReversedPath C hC x y) := rightToReversedPath_weak C hC x y
  have hhm := vertices_nonempty_iff_of_weakEquivalence (realizedConstants (homAction C hC x y))
  have hrm := vertices_nonempty_iff_of_weakEquivalence (rightConeToMixed C hC x y)
  have hrp := vertices_nonempty_iff_of_weakEquivalence (rightToReversedPath C hC x y)
  have : (node0 C hC).V.KanComplex := DaggerNativeOriginalRealSigmaUnitaryEndpoint.nerve_kan C hC
  have hp := DaggerNativeOriginalEC2PathActionExistence.realized_path_vertices_iff
    (node0 C hC) (generatorMap C hC) (generatorMap_square C hC) y x
    (fixed0 C hC y) (fixed0 C hC x) (generatorMap_eq_original C hC).symm
  exact hhm.trans (hrm.symm.trans (hrp.trans (hp.trans ⟨Eq.symm, Eq.symm⟩)))

theorem canonical_ambient_iff_full_vertex :
    SSet.π₀.mk (canonicalZero (node0 C hC) x (fixed0 C hC x)) =
        SSet.π₀.mk (canonicalZero (node0 C hC) y (fixed0 C hC y)) ↔
      SSet.π₀.mk (sourceVertex C hC x) = SSet.π₀.mk (sourceVertex C hC y) := by
  let V := vertices (node0 C hC) (v0 C hC) (fixed0 C hC)
  let i := (fullVertexSubcomplex (mappingFunctor.obj (node0 C hC)) V).ι
  have hi := DaggerOriginalFullVertexWeakEquivalenceRestriction.inclusion_mapπ₀_injective V
  have hx : SSet.mapπ₀ i (SSet.π₀.mk (sourceVertex C hC x)) =
      SSet.π₀.mk (canonicalZero (node0 C hC) x (fixed0 C hC x)) := by
    rw [SSet.mapπ₀_mk]
    rfl
  have hy : SSet.mapπ₀ i (SSet.π₀.mk (sourceVertex C hC y)) =
      SSet.π₀.mk (canonicalZero (node0 C hC) y (fixed0 C hC y)) := by
    rw [SSet.mapπ₀_mk]
    rfl
  rw [← hx, ← hy]
  exact hi.eq_iff

theorem derived_vertices_iff_original_unitary :
    Nonempty ((strictDerivedMapping C hC (label C x) (label C y)) _⦋0⦌) ↔
      SSet.π₀.mk (canonicalUnitaryVertex (DaggerNerve.daggerCoherentNerve.obj C) x) =
        SSet.π₀.mk (canonicalUnitaryVertex (DaggerNerve.daggerCoherentNerve.obj C) y) :=
  (derived_vertices_iff_realized_hom C hC x y).trans
    ((realized_hom_vertices_iff_canonical C hC x y).trans
      ((canonical_ambient_iff_full_vertex C hC x y).trans
        (DaggerNativeOriginalRealSigmaUnitaryComponents.same_component_iff C hC x y)))

end
end DaggerNativeOriginalStrictHomUnitaryExistence
