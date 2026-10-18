import NativeOriginalRealSigmaUnitaryLocalized
import NativeKanWeakComponents

/-! Components of the literal original Sigma EC2 complex and EXACT ORIGINAL unitary core. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial HomotopicalAlgebra DaggerModels OrdinaryRigidification
open DaggerNativeOriginalRealSigmaAnchors DaggerNativeOriginalRealSigmaCanonicalZigzag
open DaggerNativeOriginalRealSigmaCanonicalEndpoint DaggerNativeOriginalRealSigmaUnitaryEndpoint
open DaggerNativeOriginalActionCanonicalRestriction DaggerNativeKanWeakComponents
open DaggerOriginalSimplicialGroupoidCompletionUniversal
open DaggerOriginalUnitaryCoreConstruction DaggerOriginalUnitaryCoreCanonicalVertices
open DaggerNativeOriginalSigmaResolutionSpan
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeOriginalRealSigmaUnitaryComponents
noncomputable section

local instance originalCanonicalKan (C : DaggerSimplicialCat.{u, u}) :
    (DaggerOriginalEC2CanonicalVertexKan.canonicalVertexFunctor.obj
      (DaggerNerve.daggerCoherentNerve.obj C)).KanComplex :=
  DaggerOriginalEC2CanonicalVertexKan.canonicalVertexSubcomplex_kan _

local instance originalUnitaryKan (C : DaggerSimplicialCat.{u, u}) :
    (unitaryCore (DaggerNerve.daggerCoherentNerve.obj C)).KanComplex := unitaryCore_kan _

def sourceVertex (C : DaggerSimplicialCat.{u, u})
    (hC : IsStrictGroupoid C.toSimplicialCat) (x : Labels C) : (K0 C hC) _⦋0⦌ :=
  canonicalVertex (node0 C hC) (v0 C hC) (fixed0 C hC) x

/-- Compose component equivalences of the SAME seven actual weak maps. -/
def comparison (C : DaggerSimplicialCat.{u, u}) (hC : IsStrictGroupoid C.toSimplicialCat) :
    (K0 C hC).π₀ ≃ (unitaryCore (DaggerNerve.daggerCoherentNerve.obj C)).π₀ :=
  let h := seven_weak C hC
  (equivalence (map01 C hC) h.1).trans <|
    (equivalence (map21 C hC) h.2.1).symm.trans <|
    (equivalence (map23 C hC) h.2.2.1).trans <|
    (equivalence (map34 C hC) h.2.2.2.1).trans <|
    (equivalence (map54 C hC) h.2.2.2.2.1).symm.trans <|
    (equivalence (finalComparison C) h.2.2.2.2.2.1).trans
      (equivalence (originalUnitaryMap C) h.2.2.2.2.2.2).symm

/-- Every original label is carried to its SAME original canonical unitary vertex. -/
theorem comparison_vertex (C : DaggerSimplicialCat.{u, u})
    (hC : IsStrictGroupoid C.toSimplicialCat) (x : Labels C) :
    comparison C hC (SSet.π₀.mk (sourceVertex C hC x)) =
      SSet.π₀.mk (canonicalUnitaryVertex (DaggerNerve.daggerCoherentNerve.obj C) x) := by
  let a0 := sourceVertex C hC x
  let a1 := canonicalVertex (node1 C hC) (v1 C hC) (fixed1 C hC) x
  let a2 := canonicalVertex (node2 C hC) (v2 C hC) (fixed2 C hC) x
  let a3 := canonicalVertex (node3 C) (v3 C hC) (fixed3 C hC) x
  let a4 := canonicalVertex (node4 C) (v4 C hC) (fixed4 C hC) x
  let a5 := canonicalVertex (node5 C) (v5 C) (fixed5 C) x
  let aU := canonicalUnitaryVertex (DaggerNerve.daggerCoherentNerve.obj C) x
  let aR := (originalUnitaryMap C).app (op ⦋0⦌) aU
  have h01 : (map01 C hC).app (op ⦋0⦌) a0 = a1 :=
    DaggerNativeOriginalActionCanonicalRestriction.map_vertex
      (v := v0 C hC) (hv := fixed0 C hC) (w := v1 C hC) (hw := fixed1 C hC)
      (coherentSigmaMap C hC) id (anchor01 C hC) x
  have h21 : (map21 C hC).app (op ⦋0⦌) a2 = a1 :=
    DaggerNativeOriginalActionCanonicalRestriction.map_vertex
      (v := v2 C hC) (hv := fixed2 C hC) (w := v1 C hC) (hw := fixed1 C hC)
      (ordinarySigmaMap C hC) id (anchor21 C hC) x
  have h23 : (map23 C hC).app (op ⦋0⦌) a2 = a3 :=
    DaggerNativeOriginalActionCanonicalRestriction.map_vertex
      (v := v2 C hC) (hv := fixed2 C hC) (w := v3 C hC) (hw := fixed3 C hC)
      (DaggerNativeOriginalPalindromicC2Bridge.comparison C hC) id (anchor23 C hC) x
  have h34 : (map34 C hC).app (op ⦋0⦌) a3 = a4 :=
    DaggerNativeOriginalActionCanonicalRestriction.map_vertex
      (v := v3 C hC) (hv := fixed3 C hC) (w := v4 C hC) (hw := fixed4 C hC)
      (DaggerNativeRealOrdinaryCotensorComparison.comparison C) id (anchor34 C hC) x
  have h54 : (map54 C hC).app (op ⦋0⦌) a5 = a4 :=
    DaggerNativeOriginalActionCanonicalRestriction.map_vertex
      (v := v5 C) (hv := fixed5 C) (w := v4 C hC) (hw := fixed4 C hC)
      (DaggerNativeRealCoherentCotensorComparison.comparisonAction C) id (anchor54 C hC) x
  have h5r : (finalComparison C).app (op ⦋0⦌) a5 = aR := by
    apply Subtype.ext
    exact (final_vertex C x).trans (originalUnitaryMap_vertex C x).symm
  let h := seven_weak C hC
  have q01 := equivalence_vertex (map01 C hC) h.1 a0 a1 h01
  have q21 := equivalence_symm_vertex (map21 C hC) h.2.1 a2 a1 h21
  have q23 := equivalence_vertex (map23 C hC) h.2.2.1 a2 a3 h23
  have q34 := equivalence_vertex (map34 C hC) h.2.2.2.1 a3 a4 h34
  have q54 := equivalence_symm_vertex (map54 C hC) h.2.2.2.2.1 a5 a4 h54
  have q5r := equivalence_vertex (finalComparison C) h.2.2.2.2.2.1 a5 aR h5r
  have qUr := equivalence_symm_vertex (originalUnitaryMap C) h.2.2.2.2.2.2 aU aR rfl
  dsimp only [comparison, Equiv.trans_apply]
  erw [q01, q21, q23, q34, q54, q5r, qUr]

/-- The comparison detects connectivity for ALL ordered original pairs, including x = y. -/
theorem same_component_iff (C : DaggerSimplicialCat.{u, u})
    (hC : IsStrictGroupoid C.toSimplicialCat) (x y : Labels C) :
    SSet.π₀.mk (sourceVertex C hC x) = SSet.π₀.mk (sourceVertex C hC y) ↔
      SSet.π₀.mk (canonicalUnitaryVertex (DaggerNerve.daggerCoherentNerve.obj C) x) =
        SSet.π₀.mk (canonicalUnitaryVertex (DaggerNerve.daggerCoherentNerve.obj C) y) := by
  rw [← comparison_vertex C hC x, ← comparison_vertex C hC y]
  exact (comparison C hC).injective.eq_iff.symm

end
end DaggerNativeOriginalRealSigmaUnitaryComponents
