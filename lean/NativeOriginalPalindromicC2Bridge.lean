import NativeOriginalPalindromicMiddle
import NativeRealOrdinaryCotensorNaturality

/-! A strict ORIGINAL-C2 weak bridge from OLD Sigma to OLD real dagger, with all vertices. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial HomotopicalAlgebra DaggerModels
open DaggerOriginalSimplicialDegreeCategory DaggerOriginalSimplicialCategoryDiagonalNerve
open DaggerOriginalSimplicialGroupoidCompletionUniversal DaggerOriginalStrictDaggerGroupoidSigma
open DaggerNativeOriginalFunctorInvolutionAction DaggerNativeOriginalPalindromicMiddle
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeOriginalPalindromicC2Bridge
noncomputable section

/-- Source is the EXACT OLD Sigma action; target is the EXACT OLD real ordinary action. -/
def comparison (C : DaggerSimplicialCat.{u, u})
    (hC : IsStrictGroupoid C.toSimplicialCat) :
    DaggerNativeCoherentResolutionC2Span.ordinaryAction
        (strictSigmaFunctor C hC) (strictSigmaFunctor_involutive C hC) ⟶
      DaggerNativeRealOrdinaryCotensorComparison.ordinaryAction C :=
  DaggerNativeOriginalC2InvolutionAction.map
    (imageEnd diagonalNerveFunctor (strictSigmaFunctor C hC))
    (image_square diagonalNerveFunctor _ (strictSigmaFunctor_involutive C hC))
    (DaggerNativeRealDaggerDiagramAction.diagonalInvolution
      (DaggerNativeDaggerDegreeNerveComparison.degreeDiagram C))
    (DaggerNativeRealDaggerDiagramAction.diagonalInvolution_square
      (DaggerNativeDaggerDegreeNerveComparison.degreeDiagram C))
    (underlyingComparison C hC) (comparison_comm C hC)

theorem comparison_weak (C : DaggerSimplicialCat.{u, u})
    (hC : IsStrictGroupoid C.toSimplicialCat) : WeakEquivalence (comparison C hC).hom :=
  DaggerNativeOriginalPalindromicMiddle.comparison_weak C hC

/-- Every whole original diagonal simplex returns unchanged through the OLD projection. -/
theorem comparison_projection (C : DaggerSimplicialCat.{u, u})
    (hC : IsStrictGroupoid C.toSimplicialCat) :
    (comparison C hC).hom ≫ projection C.toSimplicialCat =
      𝟙 (diagonalNerveFunctor.obj C.toSimplicialCat) :=
  DaggerNativeOriginalPalindromicMiddle.comparison_projection C hC

/-- Every original vertex becomes its SAME canonical identity-arrow vertex. -/
theorem comparison_vertex (C : DaggerSimplicialCat.{u, u})
    (hC : IsStrictGroupoid C.toSimplicialCat)
    (x : degreeObjects C.toSimplicialCat (op ⦋0⦌)) :
    (comparison C hC).hom.app (op ⦋0⦌) (ComposableArrows.mk₀ x) =
      (nerve (degreeObjects C.toSimplicialCat (op ⦋0⦌))).σ (0 : Fin 1)
        (ComposableArrows.mk₀ x) := by
  letI := strictDegreeGroupoid C.toSimplicialCat hC (op ⦋0⦌)
  exact DaggerNativeGroupoidPalindromicSection.section_vertex
    (degreeObjects C.toSimplicialCat (op ⦋0⦌)) x

/-- ALL original dagger functors preserve the ENTIRE strict equivariant bridge. -/
theorem comparison_naturality {C D : DaggerSimplicialCat.{u, u}}
    (hC : IsStrictGroupoid C.toSimplicialCat) (hD : IsStrictGroupoid D.toSimplicialCat)
    (P : C ⟶ D) :
    comparison C hC ≫ DaggerNativeRealOrdinaryCotensorNaturality.coefficientMap P =
      DaggerNativeOriginalSigmaResolutionSpan.sigmaCoefficientMap
        diagonalNerveFunctor hC hD P ≫ comparison D hD := by
  apply Action.hom_ext
  apply NatTrans.ext
  funext n F
  letI := strictDegreeGroupoid C.toSimplicialCat hC n
  letI := strictDegreeGroupoid D.toSimplicialCat hD n
  exact (congrFun (NatTrans.congr_app
    (DaggerNativeGroupoidPalindromicNaturality.section_naturality
      (degreeFunctor P.toEnrichedFunctor n)) n) F).symm

end
end DaggerNativeOriginalPalindromicC2Bridge
