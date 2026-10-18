import NativeOriginalRealSigmaUnitaryEndpoint
import NativeOriginalKanLocalizedPointIso

/-! The SAME seven weak arrows give a point-preserving iso to EXACT ORIGINAL U. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial HomotopicalAlgebra DaggerModels OrdinaryRigidification
open DaggerNativeOriginalRealSigmaAnchors DaggerNativeOriginalRealSigmaCanonicalZigzag
open DaggerNativeOriginalRealSigmaCanonicalEndpoint DaggerNativeOriginalRealSigmaUnitaryEndpoint
open DaggerNativeOriginalActionCanonicalRestriction DaggerNativeOriginalKanLocalizedPointIso
open DaggerOriginalSimplicialGroupoidCompletionUniversal DaggerNativeOriginalRReplacedMapping
open DaggerOriginalUnitaryCoreConstruction DaggerOriginalUnitaryCoreCanonicalVertices
open DaggerNativeOriginalSigmaResolutionSpan
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeOriginalRealSigmaUnitaryLocalized
noncomputable section

/-- Use the ORIGINAL weak localization and the actual seven original weak maps. -/
def comparisonIso (C : DaggerSimplicialCat.{u, u}) (hC : IsStrictGroupoid C.toSimplicialCat) :
    kanWeak.Q.obj (K0 C hC) ≅ kanWeak.Q.obj (unitaryCore (DaggerNerve.daggerCoherentNerve.obj C)) :=
  let h := seven_weak C hC
  mapIso (map01 C hC) h.1 ≪≫ (mapIso (map21 C hC) h.2.1).symm ≪≫
    mapIso (map23 C hC) h.2.2.1 ≪≫ mapIso (map34 C hC) h.2.2.2.1 ≪≫
    (mapIso (map54 C hC) h.2.2.2.2.1).symm ≪≫
    mapIso (finalComparison C) h.2.2.2.2.2.1 ≪≫
    (mapIso (originalUnitaryMap C) h.2.2.2.2.2.2).symm

/-- A SINGLE comparison iso carries EVERY SAME original point to its ORIGINAL U vertex. -/
theorem comparisonIso_point (C : DaggerSimplicialCat.{u, u})
    (hC : IsStrictGroupoid C.toSimplicialCat) (x : Labels C) :
    kanWeak.Q.map (SSet.yonedaEquiv.symm
      (canonicalVertex (node0 C hC) (v0 C hC) (fixed0 C hC) x)) ≫ (comparisonIso C hC).hom =
        kanWeak.Q.map (SSet.yonedaEquiv.symm
          (canonicalUnitaryVertex (DaggerNerve.daggerCoherentNerve.obj C) x)) := by
  let a0 := canonicalVertex (node0 C hC) (v0 C hC) (fixed0 C hC) x
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
  have q01 := point_hom (map01 C hC) h.1 a0 a1 h01
  have q21 := point_inv (map21 C hC) h.2.1 a2 a1 h21
  have q23 := point_hom (map23 C hC) h.2.2.1 a2 a3 h23
  have q34 := point_hom (map34 C hC) h.2.2.2.1 a3 a4 h34
  have q54 := point_inv (map54 C hC) h.2.2.2.2.1 a5 a4 h54
  have q5r := point_hom (finalComparison C) h.2.2.2.2.2.1 a5 aR h5r
  have qUr := point_inv (originalUnitaryMap C) h.2.2.2.2.2.2 aU aR rfl
  dsimp only [comparisonIso, Iso.trans_hom, Iso.symm_hom]
  simp only [← Category.assoc]
  erw [q01, q21, q23, q34, q54, q5r, qUr]

end
end DaggerNativeOriginalRealSigmaUnitaryLocalized
