import NativeOriginalRealSigmaAnchors

/-! The ORIGINAL EC2 mapping zigzag, restricted to ALL SAME original canonical vertices. -/
set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra DaggerModels
open DaggerOriginalSimplicialGroupoidCompletionUniversal
open DaggerNativeOriginalRealSigmaAnchors DaggerNativeOriginalSigmaResolutionSpan
open DaggerNativeOriginalActionCanonicalRestriction
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeOriginalRealSigmaCanonicalZigzag
noncomputable section

variable (C : DaggerSimplicialCat.{u, u}) (hC : IsStrictGroupoid C.toSimplicialCat)

def K0 : SSet.{u} := (canonicalSubcomplex (node0 C hC) (v0 C hC) (fixed0 C hC)).toSSet
def K1 : SSet.{u} := (canonicalSubcomplex (node1 C hC) (v1 C hC) (fixed1 C hC)).toSSet
def K2 : SSet.{u} := (canonicalSubcomplex (node2 C hC) (v2 C hC) (fixed2 C hC)).toSSet
def K3 : SSet.{u} := (canonicalSubcomplex (node3 C) (v3 C hC) (fixed3 C hC)).toSSet
def K4 : SSet.{u} := (canonicalSubcomplex (node4 C) (v4 C hC) (fixed4 C hC)).toSSet
def K5 : SSet.{u} := (canonicalSubcomplex (node5 C) (v5 C) (fixed5 C)).toSSet

instance kan0 : (K0 C hC).KanComplex := by unfold K0; infer_instance
instance kan1 : (K1 C hC).KanComplex := by unfold K1; infer_instance
instance kan2 : (K2 C hC).KanComplex := by unfold K2; infer_instance
instance kan3 : (K3 C hC).KanComplex := by unfold K3; infer_instance
instance kan4 : (K4 C hC).KanComplex := by unfold K4; infer_instance
instance kan5 : (K5 C).KanComplex := by unfold K5; infer_instance

def map01 : K0 C hC ⟶ K1 C hC :=
  DaggerNativeOriginalActionCanonicalRestriction.map
    (v := v0 C hC) (hv := fixed0 C hC) (w := v1 C hC) (hw := fixed1 C hC)
    (coherentSigmaMap C hC) id (anchor01 C hC)

def map21 : K2 C hC ⟶ K1 C hC :=
  DaggerNativeOriginalActionCanonicalRestriction.map
    (v := v2 C hC) (hv := fixed2 C hC) (w := v1 C hC) (hw := fixed1 C hC)
    (ordinarySigmaMap C hC) id (anchor21 C hC)

def map23 : K2 C hC ⟶ K3 C hC :=
  DaggerNativeOriginalActionCanonicalRestriction.map
    (v := v2 C hC) (hv := fixed2 C hC) (w := v3 C hC) (hw := fixed3 C hC)
    (DaggerNativeOriginalPalindromicC2Bridge.comparison C hC) id (anchor23 C hC)

def map34 : K3 C hC ⟶ K4 C hC :=
  DaggerNativeOriginalActionCanonicalRestriction.map
    (v := v3 C hC) (hv := fixed3 C hC) (w := v4 C hC) (hw := fixed4 C hC)
    (DaggerNativeRealOrdinaryCotensorComparison.comparison C) id (anchor34 C hC)

def map54 : K5 C ⟶ K4 C hC :=
  DaggerNativeOriginalActionCanonicalRestriction.map
    (v := v5 C) (hv := fixed5 C) (w := v4 C hC) (hw := fixed4 C hC)
    (DaggerNativeRealCoherentCotensorComparison.comparisonAction C) id (anchor54 C hC)

/-- ALL FIVE weak maps are the SAME literal OLD EC2 maps restricted at SAME original points. -/
theorem five_weak : WeakEquivalence (map01 C hC) ∧ WeakEquivalence (map21 C hC) ∧
    WeakEquivalence (map23 C hC) ∧ WeakEquivalence (map34 C hC) ∧
    WeakEquivalence (map54 C hC) := by
  obtain ⟨h01, h21, h23, h34, h54⟩ := DaggerNativeOriginalRealSigmaZigzag.five_weak C hC
  have : WeakEquivalence (coherentSigmaMap C hC).hom := h01
  have : WeakEquivalence (ordinarySigmaMap C hC).hom := h21
  have : WeakEquivalence (DaggerNativeOriginalPalindromicC2Bridge.comparison C hC).hom := h23
  have : WeakEquivalence (DaggerNativeRealOrdinaryCotensorComparison.comparison C).hom := h34
  have : WeakEquivalence (DaggerNativeRealCoherentCotensorComparison.comparisonAction C).hom := h54
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact DaggerNativeOriginalActionCanonicalRestriction.map_weak
      (v := v0 C hC) (hv := fixed0 C hC) (w := v1 C hC) (hw := fixed1 C hC)
      (coherentSigmaMap C hC) id (anchor01 C hC) (fun x ↦ ⟨x, rfl⟩)
  · exact DaggerNativeOriginalActionCanonicalRestriction.map_weak
      (v := v2 C hC) (hv := fixed2 C hC) (w := v1 C hC) (hw := fixed1 C hC)
      (ordinarySigmaMap C hC) id (anchor21 C hC) (fun x ↦ ⟨x, rfl⟩)
  · exact DaggerNativeOriginalActionCanonicalRestriction.map_weak
      (v := v2 C hC) (hv := fixed2 C hC) (w := v3 C hC) (hw := fixed3 C hC)
      (DaggerNativeOriginalPalindromicC2Bridge.comparison C hC) id (anchor23 C hC)
      (fun x ↦ ⟨x, rfl⟩)
  · exact DaggerNativeOriginalActionCanonicalRestriction.map_weak
      (v := v3 C hC) (hv := fixed3 C hC) (w := v4 C hC) (hw := fixed4 C hC)
      (DaggerNativeRealOrdinaryCotensorComparison.comparison C) id (anchor34 C hC)
      (fun x ↦ ⟨x, rfl⟩)
  · exact DaggerNativeOriginalActionCanonicalRestriction.map_weak
      (v := v5 C) (hv := fixed5 C) (w := v4 C hC) (hw := fixed4 C hC)
      (DaggerNativeRealCoherentCotensorComparison.comparisonAction C) id (anchor54 C hC)
      (fun x ↦ ⟨x, rfl⟩)

end
end DaggerNativeOriginalRealSigmaCanonicalZigzag
