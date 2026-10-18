import NativeOriginalSigmaResolutionSpan
import NativeRealOrdinaryCotensorComparison

/-! Independently fix the canonical ORIGINAL vertex in all four OLD outer comparison legs. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial DaggerModels OrdinaryRigidification
open DaggerOriginalSimplicialDegreeCategory DaggerOriginalCotensorPrecompositionWeak
open DaggerOriginalSimplicialGroupoidCompletionUniversal DaggerNativeOriginalSigmaResolutionSpan
universe u
namespace DaggerChallengeOriginalRealSigmaVertices
noncomputable section

def vertex (C : SimplicialCat.{u, u}) (x : C.Obj) :
    (coherentNerve.obj C).obj (op ⦋0⦌) := (NerveVertices.vertexEquiv C).symm x

def cotensorVertex (C : SimplicialCat.{u, u}) (x : C.Obj) :=
  vertex (originalCotensor (SSet.stdSimplex.obj ⦋0⦌) C) x

def Statement : Prop :=
  ∀ (C : DaggerSimplicialCat.{u, u}) (hC : IsStrictGroupoid C.toSimplicialCat) (x : C.Obj),
    (coherentSigmaMap C hC).hom.app (op ⦋0⦌) (vertex C.toSimplicialCat x) =
        cotensorVertex C.toSimplicialCat x ∧
    (ordinarySigmaMap C hC).hom.app (op ⦋0⦌) (ComposableArrows.mk₀ x) =
        cotensorVertex C.toSimplicialCat x ∧
    (DaggerNativeRealOrdinaryCotensorComparison.comparison C).hom.app (op ⦋0⦌)
        ((nerve (degreeObjects C.toSimplicialCat (op ⦋0⦌))).σ (0 : Fin 1)
          (ComposableArrows.mk₀ x)) =
      (coherentNerve.obj (originalCotensor (SSet.stdSimplex.obj ⦋0⦌) C.toSimplicialCat)).σ
        (0 : Fin 1) (cotensorVertex C.toSimplicialCat x) ∧
    (DaggerNativeRealCoherentCotensorComparison.comparisonAction C).hom.app (op ⦋0⦌)
        ((coherentNerve.obj C.toSimplicialCat).σ (0 : Fin 1) (vertex C.toSimplicialCat x)) =
      (coherentNerve.obj (originalCotensor (SSet.stdSimplex.obj ⦋0⦌) C.toSimplicialCat)).σ
        (0 : Fin 1) (cotensorVertex C.toSimplicialCat x)

end
end DaggerChallengeOriginalRealSigmaVertices
