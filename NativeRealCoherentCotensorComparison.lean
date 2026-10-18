import NativeDaggerCotensorResolution
import NativeRealEdgewiseC2Action
import NativeEdgewiseMapWeak
import NativeCoherentCotensorResolutionWeak

/-! A weak equivariant comparison for the ORIGINAL real OUTER dagger action. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial HomotopicalAlgebra DaggerModels OrdinaryRigidification
open DaggerNativeRealEdgewiseSSet DaggerNativeRealEdgewiseDaggerInvolution
open DaggerNativeBisimplicialDiagonal DaggerOriginalCoherentCotensorResolution
open DaggerOriginalAmbientDaggerPiZeroGroupoid DaggerOriginalDaggerRealizationC2Action
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeRealCoherentCotensorComparison
noncomputable section

/-- Edgewise is applied to the outer coherent nerve, before taking the diagonal. -/
def underlyingDiagram (C : DaggerSimplicialCat.{u, u}) :
    SimplexCategoryᵒᵖ ⥤ SSet.{u} := resolution C.toSimplicialCat ⋙ edgewise

/-- The parameter index is fixed and the original outer dagger acts in each column. -/
def diagramInvolution (C : DaggerSimplicialCat.{u, u}) :
    underlyingDiagram C ⟶ underlyingDiagram C where
  app n := involution ((DaggerNativeDaggerCotensorResolution.resolution C).obj n)
  naturality _ _ a :=
    (involution_natural ((DaggerNativeDaggerCotensorResolution.resolution C).map a)).symm

theorem diagramInvolution_square (C : DaggerSimplicialCat.{u, u}) :
    diagramInvolution C ≫ diagramInvolution C = 𝟙 _ := by
  apply NatTrans.ext
  funext n
  exact involution_square ((DaggerNativeDaggerCotensorResolution.resolution C).obj n)

def diagonalInvolution (C : DaggerSimplicialCat.{u, u}) :
    End (diagonalFunctor.obj (underlyingDiagram C)) :=
  End.of (diagonalFunctor.map (diagramInvolution C))

theorem diagonalInvolution_square (C : DaggerSimplicialCat.{u, u}) :
    diagonalInvolution C * diagonalInvolution C = 1 := by
  change diagonalFunctor.map (diagramInvolution C) ≫
    diagonalFunctor.map (diagramInvolution C) = 𝟙 _
  rw [← diagonalFunctor.map_comp, diagramInvolution_square, diagonalFunctor.map_id]

/-- The group and all its action laws are the unchanged original C2. -/
def action (C : DaggerSimplicialCat.{u, u}) : Action SSet.{u} C2.{u} :=
  DaggerNativeOriginalC2InvolutionAction.action
    (diagonalInvolution C) (diagonalInvolution_square C)

/-- The underlying map is precisely the old constants with outer edgewise applied. -/
def comparison (C : DaggerSimplicialCat.{u, u}) :
    edgewise.obj (coherentNerve.obj C.toSimplicialCat) ⟶
      diagonalFunctor.obj (underlyingDiagram C) :=
  (diagonalConstantIso (edgewise.obj (coherentNerve.obj C.toSimplicialCat))).inv ≫
    diagonalFunctor.map (Functor.whiskerRight (constantComparison C.toSimplicialCat) edgewise)

/-- The entire comparison intertwines the actual outer dagger involutions. -/
theorem comparison_comm (C : DaggerSimplicialCat.{u, u}) :
    involution (DaggerNerve.daggerCoherentNerve.obj C) ≫ comparison C =
      comparison C ≫ (diagonalInvolution C).asHom := by
  apply NatTrans.ext
  funext n p
  exact congrFun (NatTrans.congr_app (involution_natural
    ((DaggerNativeDaggerCotensorResolution.constantComparison C).app n)) n) p

/-- This is a strict original-C2 map, not merely an underlying weak map. -/
def comparisonAction (C : DaggerSimplicialCat.{u, u}) :
    DaggerNativeRealEdgewiseC2Action.action (DaggerNerve.daggerCoherentNerve.obj C) ⟶
      action C :=
  DaggerNativeOriginalC2InvolutionAction.map
    (DaggerNativeRealEdgewiseC2Action.involutionEnd (DaggerNerve.daggerCoherentNerve.obj C))
    (DaggerNativeRealEdgewiseC2Action.involutionEnd_square
      (DaggerNerve.daggerCoherentNerve.obj C))
    (diagonalInvolution C) (diagonalInvolution_square C) (comparison C) (comparison_comm C)

/-- The original real comparison is weak under exactly the old local Kan/groupoid input. -/
theorem comparison_weak (C : DaggerSimplicialCat.{u, u})
    (hC : ∀ x y : C.Obj, SSet.KanComplex (C.enriched.Hom x y))
    (hG : HasActualComponentGroupoid C.toSimplicialCat) :
    WeakEquivalence (comparisonAction C).hom := by
  have hw : ∀ n, WeakEquivalence (edgewise.map
      ((constantComparison C.toSimplicialCat).app n)) := by
    intro n
    have := DaggerNativeCoherentCotensorResolutionWeak.constantComparison_app_weak
      C.toSimplicialCat hC hG n
    exact DaggerNativeEdgewiseMapWeak.map_weak _
  have : WeakEquivalence (diagonalFunctor.map
      (Functor.whiskerRight (constantComparison C.toSimplicialCat) edgewise)) :=
    DaggerNativeBisimplicialDiagonalWeak.diagonal_map_weak _ hw
  change WeakEquivalence
    ((diagonalConstantIso (edgewise.obj (coherentNerve.obj C.toSimplicialCat))).inv ≫ _)
  infer_instance

end
end DaggerNativeRealCoherentCotensorComparison
