import NativeOriginalPalindromicC2Bridge

/-! All FIVE actual original-C2 weak legs, with NO extra hypothesis on strict groupoids. -/
set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra DaggerModels
open DaggerOriginalSimplicialGroupoidCompletionUniversal
open DaggerOriginalStrictSimplicialGroupoidMappingKan DaggerOriginalStrictSimplicialPiZeroGroupoid
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeOriginalRealSigmaZigzag
noncomputable section

/-- The full original Sigma/real resolution zigzag has five weak equivariant legs. -/
theorem five_weak (C : DaggerSimplicialCat.{u, u})
    (hC : IsStrictGroupoid C.toSimplicialCat) :
    WeakEquivalence (DaggerNativeOriginalSigmaResolutionSpan.coherentSigmaMap C hC).hom ∧
    WeakEquivalence (DaggerNativeOriginalSigmaResolutionSpan.ordinarySigmaMap C hC).hom ∧
    WeakEquivalence (DaggerNativeOriginalPalindromicC2Bridge.comparison C hC).hom ∧
    WeakEquivalence (DaggerNativeRealOrdinaryCotensorComparison.comparison C).hom ∧
    WeakEquivalence (DaggerNativeRealCoherentCotensorComparison.comparisonAction C).hom := by
  have hH : ∀ x y : C.Obj, SSet.KanComplex (C.enriched.Hom x y) :=
    strictHom_kan C.toSimplicialCat hC
  have hG : DaggerOriginalAmbientDaggerPiZeroGroupoid.HasActualComponentGroupoid
      C.toSimplicialCat :=
    ⟨strictComponentGroupoid C.toSimplicialCat hC,
      strictComponentGroupoid_category C.toSimplicialCat hC⟩
  exact ⟨DaggerNativeOriginalSigmaResolutionSpan.coherentSigmaMap_weak C hC hH,
    DaggerNativeOriginalSigmaResolutionSpan.ordinarySigmaMap_weak C hC,
    DaggerNativeOriginalPalindromicC2Bridge.comparison_weak C hC,
    DaggerNativeRealOrdinaryCotensorComparison.comparison_weak C,
    DaggerNativeRealCoherentCotensorComparison.comparison_weak C hH hG⟩

end
end DaggerNativeOriginalRealSigmaZigzag
