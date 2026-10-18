import NativeOriginalRealSigmaCanonicalEndpoint
import NativeOriginalKanUnitaryCanonicalIso

/-! The actual endpoint is the EXACT ORIGINAL U of the SAME original strict dagger nerve. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial HomotopicalAlgebra DaggerModels OrdinaryRigidification
open DaggerOriginalSimplicialGroupoidCompletionUniversal
open DaggerOriginalStrictSimplicialGroupoidMappingKan DaggerOriginalStrictSimplicialPiZeroGroupoid
open DaggerOriginalDaggerCoreCandidate DaggerOriginalUnitaryCoreConstruction
open DaggerOriginalUnitaryCoreCanonicalVertices DaggerOriginalEC2CanonicalVertexKan
open DaggerOriginalEC2CanonicalVertexSubcomplex DaggerOriginalEC2HomotopyFixedPointObject
open DaggerNativeOriginalRealSigmaAnchors DaggerNativeOriginalRealSigmaCanonicalZigzag
open DaggerNativeOriginalRealSigmaCanonicalEndpoint DaggerNativeOriginalKanUnitaryCanonicalIso
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeOriginalRealSigmaUnitaryEndpoint
noncomputable section

/-- Strictness supplies ALL required original Kan input, without a new hypothesis. -/
theorem nerve_kan (C : DaggerSimplicialCat.{u, u})
    (hC : IsStrictGroupoid C.toSimplicialCat) :
    (DaggerNerve.daggerCoherentNerve.obj C).toSSet.KanComplex :=
  DaggerActualLocallyKanGroupoidalCoherentNerve.kan C.toSimplicialCat
    (strictHom_kan C.toSimplicialCat hC)
    ⟨strictComponentGroupoid C.toSimplicialCat hC,
      strictComponentGroupoid_category C.toSimplicialCat hC⟩

/-- The arrow is exactly the OLD canonical map of the ORIGINAL greatest dagger core inclusion. -/
def originalUnitaryMap (C : DaggerSimplicialCat.{u, u}) :
    unitaryCore (DaggerNerve.daggerCoherentNerve.obj C) ⟶
      canonicalVertexFunctor.obj (DaggerNerve.daggerCoherentNerve.obj C) :=
  canonicalVertexMap (daggerCoreInclusion (DaggerNerve.daggerCoherentNerve.obj C))

theorem originalUnitaryMap_isIso (C : DaggerSimplicialCat.{u, u})
    (hC : IsStrictGroupoid C.toSimplicialCat) : IsIso (originalUnitaryMap C) := by
  have := nerve_kan C hC
  change IsIso (unitaryCanonicalIso (DaggerNerve.daggerCoherentNerve.obj C)).hom
  infer_instance

theorem originalUnitaryMap_weak (C : DaggerSimplicialCat.{u, u})
    (hC : IsStrictGroupoid C.toSimplicialCat) : WeakEquivalence (originalUnitaryMap C) := by
  have := originalUnitaryMap_isIso C hC
  infer_instance

/-- The endpoint uses the SAME original canonical unitary vertex and literal EC2 constant. -/
theorem originalUnitaryMap_vertex (C : DaggerSimplicialCat.{u, u}) (x : Labels C) :
    ((originalUnitaryMap C).app (op ⦋0⦌)
      (canonicalUnitaryVertex (DaggerNerve.daggerCoherentNerve.obj C) x)).val =
        canonicalZeroSimplex (DaggerNerve.daggerCoherentNerve.obj C) x := by
  change (DaggerOriginalEC2HomotopyFixedPointFunctor.daggerHomotopyFixedPointFunctor.map
    (daggerCoreInclusion (DaggerNerve.daggerCoherentNerve.obj C))).app (op ⦋0⦌)
      (canonicalZeroSimplex (daggerCoreCandidate (DaggerNerve.daggerCoherentNerve.obj C))
        ((coreVertexEquiv (DaggerNerve.daggerCoherentNerve.obj C)).symm x)) = _
  exact canonicalZeroSimplex_naturality
    (daggerCoreInclusion (DaggerNerve.daggerCoherentNerve.obj C))
    ((coreVertexEquiv (DaggerNerve.daggerCoherentNerve.obj C)).symm x)

/-- SEVEN actual weak legs end at ORIGINAL U, with the SAME original points throughout. -/
theorem seven_weak (C : DaggerSimplicialCat.{u, u}) (hC : IsStrictGroupoid C.toSimplicialCat) :
    WeakEquivalence (map01 C hC) ∧ WeakEquivalence (map21 C hC) ∧
    WeakEquivalence (map23 C hC) ∧ WeakEquivalence (map34 C hC) ∧
    WeakEquivalence (map54 C hC) ∧ WeakEquivalence (finalComparison C) ∧
    WeakEquivalence (originalUnitaryMap C) := by
  obtain ⟨h01, h21, h23, h34, h54, h5r⟩ := six_weak C hC
  exact ⟨h01, h21, h23, h34, h54, h5r, originalUnitaryMap_weak C hC⟩

end
end DaggerNativeOriginalRealSigmaUnitaryEndpoint
