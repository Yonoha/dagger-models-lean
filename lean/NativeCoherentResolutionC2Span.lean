import NativeCoherentResolutionFunctor
import NativeOriginalFunctorInvolutionAction
import NativeOrdinaryCoherentResolutionWeak
import NativeCoherentCotensorResolutionWeak

/-! The SAME two original weak comparison maps as strict actions of the ORIGINAL C2. -/
set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra Opposite Simplicial DaggerModels OrdinaryRigidification
open DaggerOriginalDaggerRealizationC2Action DaggerOriginalSimplicialCategoryDiagonalNerve
open DaggerNativeCoherentResolutionFunctor DaggerNativeOriginalFunctorInvolutionAction
open DaggerOriginalAmbientDaggerPiZeroGroupoid DaggerOriginalCotensorPrecompositionWeak
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeCoherentResolutionC2Span
noncomputable section
variable {C D : SimplicialCat.{u, u}}

abbrev coherentAction (F : C ⟶ C) (hF : F ≫ F = 𝟙 C) := actionOf coherentNerve F hF
abbrev ordinaryAction (F : C ⟶ C) (hF : F ≫ F = 𝟙 C) := actionOf diagonalNerveFunctor F hF
abbrev middleAction (F : C ⟶ C) (hF : F ≫ F = 𝟙 C) :=
  actionOf diagonalResolutionFunctor F hF

/-- Its underlying map is exactly the existing original coherent comparison. -/
def coherentMap (F : C ⟶ C) (hF : F ≫ F = 𝟙 C) :
    coherentAction F hF ⟶ middleAction F hF := naturalMap coherentComparison F hF

/-- Its underlying map is exactly the existing original ordinary diagonal comparison. -/
def ordinaryMap (F : C ⟶ C) (hF : F ≫ F = 𝟙 C) :
    ordinaryAction F hF ⟶ middleAction F hF := naturalMap ordinaryComparison F hF

theorem coherentMap_hom (F : C ⟶ C) (hF : F ≫ F = 𝟙 C) :
    (coherentMap F hF).hom = DaggerOriginalCoherentCotensorResolution.comparison C := rfl

theorem ordinaryMap_hom (F : C ⟶ C) (hF : F ≫ F = 𝟙 C) :
    (ordinaryMap F hF).hom = DaggerNativeDegreeCotensorDiagonal.diagonalComparison C := rfl

/-- The original locally Kan/groupoidal hypotheses suffice for the SAME coherent leg. -/
theorem coherentMap_weak (F : C ⟶ C) (hF : F ≫ F = 𝟙 C)
    (hC : ∀ x y : C.Obj, SSet.KanComplex (C.enriched.Hom x y))
    (hG : HasActualComponentGroupoid C) : WeakEquivalence (coherentMap F hF).hom :=
  DaggerNativeCoherentCotensorResolutionWeak.comparison_weak C hC hG

/-- The SAME ordinary leg is weak with no extra target hypothesis. -/
theorem ordinaryMap_weak (F : C ⟶ C) (hF : F ≫ F = 𝟙 C) :
    WeakEquivalence (ordinaryMap F hF).hom :=
  DaggerNativeOrdinaryCoherentResolutionWeak.diagonalComparison_weak C

/-- Entire strict-action naturality for ALL original intertwining enriched functors. -/
theorem coherentMap_naturality (F : C ⟶ C) (hF : F ≫ F = 𝟙 C)
    (G : D ⟶ D) (hG : G ≫ G = 𝟙 D) (P : C ⟶ D) (hP : F ≫ P = P ≫ G) :
    coherentMap F hF ≫ coefficientMap diagonalResolutionFunctor F hF G hG P hP =
      coefficientMap coherentNerve F hF G hG P hP ≫ coherentMap G hG :=
  naturalMap_naturality coherentComparison F hF G hG P hP

theorem ordinaryMap_naturality (F : C ⟶ C) (hF : F ≫ F = 𝟙 C)
    (G : D ⟶ D) (hG : G ≫ G = 𝟙 D) (P : C ⟶ D) (hP : F ≫ P = P ≫ G) :
    ordinaryMap F hF ≫ coefficientMap diagonalResolutionFunctor F hF G hG P hP =
      coefficientMap diagonalNerveFunctor F hF G hG P hP ≫ ordinaryMap G hG :=
  naturalMap_naturality ordinaryComparison F hF G hG P hP

/-- The strict-action map retains EVERY original coherent vertex. -/
theorem coherentMap_vertex (F : C ⟶ C) (hF : F ≫ F = 𝟙 C)
    (x : (coherentNerve.obj C).obj (op ⦋0⦌)) :
    NerveVertices.vertexEquiv (originalCotensor (SSet.stdSimplex.obj ⦋0⦌) C)
      ((coherentMap F hF).hom.app (op ⦋0⦌) x) = NerveVertices.vertexEquiv C x :=
  DaggerOriginalCoherentCotensorResolution.comparison_vertex C x

/-- Repeated original ordinary vertices are retained, with no injectivity premise. -/
theorem ordinaryMap_vertex (F : C ⟶ C) (hF : F ≫ F = 𝟙 C)
    (p : (diagonalNerveFunctor.obj C).obj (op ⦋0⦌)) :
    NerveVertices.vertexEquiv (originalCotensor (SSet.stdSimplex.obj ⦋0⦌) C)
      ((ordinaryMap F hF).hom.app (op ⦋0⦌) p) = p.obj 0 :=
  DaggerNativeDegreeCotensorDiagonal.diagonalComparison_vertex C p

end
end DaggerNativeCoherentResolutionC2Span
