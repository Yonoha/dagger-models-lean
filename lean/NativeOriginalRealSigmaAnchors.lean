import NativeOriginalActionCanonicalRestriction
import NativeOriginalRealSigmaZigzag
import NativeOriginalRealSigmaVertices

/-! Exact action-fixed ORIGINAL vertices in the SAME six objects of the original zigzag. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial DaggerModels OrdinaryRigidification
open DaggerOriginalDaggerRealizationC2Action DaggerOriginalCompletedDaggerMappingAction
open DaggerOriginalSimplicialDegreeCategory DaggerOriginalSimplicialCategoryDiagonalNerve
open DaggerOriginalSimplicialGroupoidCompletionUniversal DaggerOriginalStrictDaggerGroupoidSigma
open DaggerNativeCoherentResolutionC2Span DaggerNativeOriginalSigmaResolutionSpan
open DaggerChallengeOriginalRealSigmaVertices
universe u
namespace DaggerNativeOriginalRealSigmaAnchors
noncomputable section

abbrev Labels (C : DaggerSimplicialCat.{u, u}) := (coherentNerve.obj C.toSimplicialCat) _⦋0⦌
def label (C : DaggerSimplicialCat.{u, u}) (x : Labels C) : C.Obj :=
  NerveVertices.vertexEquiv C.toSimplicialCat x

abbrev node0 (C : DaggerSimplicialCat.{u, u}) (hC : IsStrictGroupoid C.toSimplicialCat) :=
  coherentAction (strictSigmaFunctor C hC) (strictSigmaFunctor_involutive C hC)
abbrev node1 (C : DaggerSimplicialCat.{u, u}) (hC : IsStrictGroupoid C.toSimplicialCat) :=
  middleAction (strictSigmaFunctor C hC) (strictSigmaFunctor_involutive C hC)
abbrev node2 (C : DaggerSimplicialCat.{u, u}) (hC : IsStrictGroupoid C.toSimplicialCat) :=
  ordinaryAction (strictSigmaFunctor C hC) (strictSigmaFunctor_involutive C hC)
abbrev node3 (C : DaggerSimplicialCat.{u, u}) :=
  DaggerNativeRealOrdinaryCotensorComparison.ordinaryAction C
abbrev node4 (C : DaggerSimplicialCat.{u, u}) :=
  DaggerNativeRealCoherentCotensorComparison.action C
abbrev node5 (C : DaggerSimplicialCat.{u, u}) :=
  DaggerNativeRealEdgewiseC2Action.action (DaggerNerve.daggerCoherentNerve.obj C)

variable (C : DaggerSimplicialCat.{u, u}) (hC : IsStrictGroupoid C.toSimplicialCat)

def v0 (x : Labels C) : (node0 C hC).V _⦋0⦌ := x
def v1 (x : Labels C) : (node1 C hC).V _⦋0⦌ := cotensorVertex C.toSimplicialCat (label C x)
def v2 (x : Labels C) : (node2 C hC).V _⦋0⦌ := ComposableArrows.mk₀ (label C x)
def v3 (x : Labels C) : (node3 C).V _⦋0⦌ :=
  (nerve (degreeObjects C.toSimplicialCat (op ⦋0⦌))).σ (0 : Fin 1) (v2 C hC x)
def v4 (x : Labels C) : (node4 C).V _⦋0⦌ :=
  (coherentNerve.obj (DaggerOriginalCotensorPrecompositionWeak.originalCotensor
    (SSet.stdSimplex.obj ⦋0⦌) C.toSimplicialCat)).σ (0 : Fin 1) (v1 C hC x)
def v5 (x : Labels C) : (node5 C).V _⦋0⦌ :=
  (coherentNerve.obj C.toSimplicialCat).σ (0 : Fin 1) x

theorem anchor01 (x : Labels C) :
    (coherentSigmaMap C hC).hom.app (op ⦋0⦌) (v0 C hC x) = v1 C hC x := by
  have h := DaggerNativeOriginalRealSigmaVertices.coherent_vertex C hC (label C x)
  simpa only [vertex, label, Equiv.symm_apply_apply] using h

theorem anchor21 (x : Labels C) :
    (ordinarySigmaMap C hC).hom.app (op ⦋0⦌) (v2 C hC x) = v1 C hC x :=
  DaggerNativeOriginalRealSigmaVertices.ordinary_vertex C hC (label C x)

theorem anchor23 (x : Labels C) :
    (DaggerNativeOriginalPalindromicC2Bridge.comparison C hC).hom.app (op ⦋0⦌)
      (v2 C hC x) = v3 C hC x :=
  DaggerNativeOriginalPalindromicC2Bridge.comparison_vertex C hC (label C x)

theorem anchor34 (x : Labels C) :
    (DaggerNativeRealOrdinaryCotensorComparison.comparison C).hom.app (op ⦋0⦌)
      (v3 C hC x) = v4 C hC x :=
  DaggerNativeOriginalRealSigmaVertices.real_ordinary_vertex C hC (label C x)

theorem anchor54 (x : Labels C) :
    (DaggerNativeRealCoherentCotensorComparison.comparisonAction C).hom.app (op ⦋0⦌)
      (v5 C x) = v4 C hC x := by
  have h := DaggerNativeOriginalRealSigmaVertices.real_coherent_vertex C hC (label C x)
  simpa only [vertex, label, Equiv.symm_apply_apply] using h

theorem fixed0 (x : Labels C) :
    ∀ g : C2.{u}, ((node0 C hC).ρ g).asHom.app (op ⦋0⦌) (v0 C hC x) = v0 C hC x := by
  intro g
  rcases originalC2_cases g with rfl | rfl
  · simp
  · exact (NerveVertices.vertexEquiv C.toSimplicialCat).injective
      (coherentSigma_generator_vertex C hC x)

theorem fixed2 (x : Labels C) :
    ∀ g : C2.{u}, ((node2 C hC).ρ g).asHom.app (op ⦋0⦌) (v2 C hC x) = v2 C hC x := by
  intro g
  rcases originalC2_cases g with rfl | rfl
  · simp
  · have hg := DaggerNativeOriginalFunctorInvolutionAction.action_generator
      diagonalNerveFunctor (strictSigmaFunctor C hC) (strictSigmaFunctor_involutive C hC)
    have hp := congrFun (NatTrans.congr_app hg (op ⦋0⦌)) (v2 C hC x)
    exact hp.trans (nerveMap_app_mk₀ (degreeFunctor (strictSigmaFunctor C hC) (op ⦋0⦌)) _)

theorem fixed5 (x : Labels C) :
    ∀ g : C2.{u}, ((node5 C).ρ g).asHom.app (op ⦋0⦌) (v5 C x) = v5 C x := by
  intro g
  rcases originalC2_cases g with rfl | rfl
  · simp
  · exact DaggerNativeRealEdgewiseC2Action.generator_fixed_vertex
      (DaggerNerve.daggerCoherentNerve.obj C) x

theorem fixed1 (x : Labels C) :
    ∀ g : C2.{u}, ((node1 C hC).ρ g).asHom.app (op ⦋0⦌) (v1 C hC x) = v1 C hC x :=
  DaggerNativeOriginalActionCanonicalRestriction.image_fixed (coherentSigmaMap C hC)
    (v0 C hC x) (fixed0 C hC x) (v1 C hC x) (anchor01 C hC x)

theorem fixed3 (x : Labels C) :
    ∀ g : C2.{u}, ((node3 C).ρ g).asHom.app (op ⦋0⦌) (v3 C hC x) = v3 C hC x :=
  DaggerNativeOriginalActionCanonicalRestriction.image_fixed
    (DaggerNativeOriginalPalindromicC2Bridge.comparison C hC)
    (v2 C hC x) (fixed2 C hC x) (v3 C hC x) (anchor23 C hC x)

theorem fixed4 (x : Labels C) :
    ∀ g : C2.{u}, ((node4 C).ρ g).asHom.app (op ⦋0⦌) (v4 C hC x) = v4 C hC x :=
  DaggerNativeOriginalActionCanonicalRestriction.image_fixed
    (DaggerNativeRealOrdinaryCotensorComparison.comparison C)
    (v3 C hC x) (fixed3 C hC x) (v4 C hC x) (anchor34 C hC x)

end
end DaggerNativeOriginalRealSigmaAnchors
