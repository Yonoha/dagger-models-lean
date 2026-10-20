import NativeOriginalDegreeSigmaAlignment
import NativePalindromicDaggerEquivariance
import NativeOriginalSigmaResolutionSpan

/-! The palindromic middle comparison on the SAME original strict degree groupoids. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial HomotopicalAlgebra DaggerModels
open DaggerOriginalSimplicialDegreeCategory DaggerOriginalSimplicialCategoryDiagonalNerve
open DaggerOriginalSimplicialGroupoidCompletionUniversal
open DaggerOriginalStrictDaggerGroupoidSigma DaggerNativeOriginalDegreeSigmaAlignment
open DaggerNativeGroupoidPalindromicSection DaggerNativeGroupoidPalindromicNaturality
open DaggerNativeDaggerDegreeCotensor DaggerNativeBisimplicialDiagonal
open DaggerNativeRealEdgewiseSSet DaggerNativeRealEdgewiseExactness
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeOriginalPalindromicMiddle
noncomputable section

/-- The original groupoid chain in each original Hom degree supplies its exact section. -/
def degreeSection (C : DaggerSimplicialCat.{u, u})
    (hC : IsStrictGroupoid C.toSimplicialCat) (n : SimplexCategoryᵒᵖ) :
    nerve (degreeObjects C.toSimplicialCat n) ⟶
      edgewise.obj (nerve (degreeObjects C.toSimplicialCat n)) := by
  letI := strictDegreeGroupoid C.toSimplicialCat hC n
  exact sectionMap (degreeObjects C.toSimplicialCat n)

/-- ALL original parameter operators preserve the entire original palindromic chain. -/
def parameterComparison (C : DaggerSimplicialCat.{u, u})
    (hC : IsStrictGroupoid C.toSimplicialCat) :
    bisimplicialNerveFunctor.obj C.toSimplicialCat ⟶
      bisimplicialNerveFunctor.obj C.toSimplicialCat ⋙ edgewise where
  app := degreeSection C hC
  naturality n m a := by
    letI := strictDegreeGroupoid C.toSimplicialCat hC n
    letI := strictDegreeGroupoid C.toSimplicialCat hC m
    exact section_naturality (degreeMap C.toSimplicialCat a)

def underlyingComparison (C : DaggerSimplicialCat.{u, u})
    (hC : IsStrictGroupoid C.toSimplicialCat) :
    diagonalNerveFunctor.obj C.toSimplicialCat ⟶
      diagonalFunctor.obj (bisimplicialNerveFunctor.obj C.toSimplicialCat ⋙ edgewise) :=
  diagonalFunctor.map (parameterComparison C hC)

/-- This is the OLD target projection, evaluated diagonally on the OLD ordinary nerve. -/
def projection (C : SimplicialCat.{u, u}) :
    diagonalFunctor.obj (bisimplicialNerveFunctor.obj C ⋙ edgewise) ⟶
      diagonalNerveFunctor.obj C :=
  diagonalFunctor.map (Functor.whiskerLeft (bisimplicialNerveFunctor.obj C) targetNatural)

/-- A strict section on ENTIRE original diagonal simplices, not only on vertices. -/
theorem comparison_projection (C : DaggerSimplicialCat.{u, u})
    (hC : IsStrictGroupoid C.toSimplicialCat) :
    underlyingComparison C hC ≫ projection C.toSimplicialCat =
      𝟙 (diagonalNerveFunctor.obj C.toSimplicialCat) := by
  apply NatTrans.ext
  funext n F
  letI := strictDegreeGroupoid C.toSimplicialCat hC n
  exact fold_projection (degreeObjects C.toSimplicialCat n) n.unop F

/-- Weakness follows in every original degree and then by the ORIGINAL diagonal theorem. -/
theorem comparison_weak (C : DaggerSimplicialCat.{u, u})
    (hC : IsStrictGroupoid C.toSimplicialCat) : WeakEquivalence (underlyingComparison C hC) := by
  apply DaggerNativeBisimplicialDiagonalWeak.diagonal_map_weak
  intro n
  letI := strictDegreeGroupoid C.toSimplicialCat hC n
  exact section_weak (degreeObjects C.toSimplicialCat n)

/-- The source generator is the EXACT OLD Sigma; the target is the EXACT OLD real action. -/
theorem comparison_comm (C : DaggerSimplicialCat.{u, u})
    (hC : IsStrictGroupoid C.toSimplicialCat) :
    diagonalNerveFunctor.map (strictSigmaFunctor C hC) ≫ underlyingComparison C hC =
      underlyingComparison C hC ≫
        (DaggerNativeRealDaggerDiagramAction.diagonalInvolution
          (DaggerNativeDaggerDegreeNerveComparison.degreeDiagram C)).asHom := by
  apply NatTrans.ext
  funext n F
  letI := strictDegreeGroupoid C.toSimplicialCat hC n
  letI := degreeDaggerCategory C n
  have h := DaggerNativePalindromicDaggerEquivariance.section_comm
    (degreeObjects C.toSimplicialCat n)
  rw [← degreeSigma_eq C hC n] at h
  exact congrFun (NatTrans.congr_app h n) F

end
end DaggerNativeOriginalPalindromicMiddle
