import NativeOriginalRealSigmaCanonicalZigzag

/-! The last endpoint is the EXACT OLD canonical EC2 complex of the ORIGINAL real nerve. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial HomotopicalAlgebra DaggerModels OrdinaryRigidification
open DaggerNativeOriginalRealSigmaAnchors DaggerNativeOriginalRealSigmaCanonicalZigzag
open DaggerOriginalSimplicialGroupoidCompletionUniversal
open DaggerNativeOriginalActionCanonicalRestriction DaggerOriginalEC2HomotopyFixedPointObject
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeOriginalRealSigmaCanonicalEndpoint
noncomputable section

/-- The whole endpoint is literally the previously fixed OLD edgewise canonical object. -/
theorem endpoint_eq (C : DaggerSimplicialCat.{u, u}) :
    K5 C = DaggerNativeRealEdgewiseCanonicalPart.canonicalFunctor.obj
      (DaggerNerve.daggerCoherentNerve.obj C) := rfl

/-- Append the SAME previously fixed map to the SAME OLD real canonical complex. -/
def finalComparison (C : DaggerSimplicialCat.{u, u}) :
    K5 C ⟶ DaggerOriginalEC2CanonicalVertexKan.canonicalVertexFunctor.obj
      (DaggerNerve.daggerCoherentNerve.obj C) :=
  DaggerNativeRealEdgewiseCanonicalPart.comparison (DaggerNerve.daggerCoherentNerve.obj C)

theorem final_weak (C : DaggerSimplicialCat.{u, u}) : WeakEquivalence (finalComparison C) :=
  DaggerNativeRealEdgewiseCanonicalWeak.comparison_weak (DaggerNerve.daggerCoherentNerve.obj C)

/-- Every original point ends at its SAME original EC2 equivariant constant map. -/
theorem final_vertex (C : DaggerSimplicialCat.{u, u}) (x : Labels C) :
    ((finalComparison C).app (op ⦋0⦌)
      (canonicalVertex (node5 C) (v5 C) (fixed5 C) x)).val =
        canonicalZeroSimplex (DaggerNerve.daggerCoherentNerve.obj C) x :=
  DaggerNativeRealEdgewiseCanonicalWeak.comparison_canonicalVertex
    (DaggerNerve.daggerCoherentNerve.obj C) x

/-- SIX weak legs now end at the actual OLD canonical real-EC2 mapping complex. -/
theorem six_weak (C : DaggerSimplicialCat.{u, u}) (hC : IsStrictGroupoid C.toSimplicialCat) :
    WeakEquivalence (map01 C hC) ∧ WeakEquivalence (map21 C hC) ∧
    WeakEquivalence (map23 C hC) ∧ WeakEquivalence (map34 C hC) ∧
    WeakEquivalence (map54 C hC) ∧ WeakEquivalence (finalComparison C) := by
  obtain ⟨h01, h21, h23, h34, h54⟩ := five_weak C hC
  exact ⟨h01, h21, h23, h34, h54, final_weak C⟩

end
end DaggerNativeOriginalRealSigmaCanonicalEndpoint
