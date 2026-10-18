import NativeRealEdgewiseC2Action
import NativeBisimplicialDiagonal

/-! Diagonalize the SAME outer real action of any original dagger simplicial diagram. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial DaggerModels
open DaggerNativeRealEdgewiseSSet DaggerNativeRealEdgewiseDaggerInvolution
open DaggerNativeBisimplicialDiagonal DaggerOriginalDaggerRealizationC2Action
universe u
namespace DaggerNativeRealDaggerDiagramAction
noncomputable section

/-- The parameter degree is retained; only the outer dagger-set degree is edgewise. -/
def underlying (A : SimplexCategoryᵒᵖ ⥤ DaggerSSet.{u}) : SimplexCategoryᵒᵖ ⥤ SSet.{u} :=
  A ⋙ DaggerSSet.forget ⋙ edgewise

def diagramInvolution (A : SimplexCategoryᵒᵖ ⥤ DaggerSSet.{u}) :
    underlying A ⟶ underlying A where
  app n := involution (A.obj n)
  naturality _ _ a := (involution_natural (A.map a)).symm

theorem diagramInvolution_square (A : SimplexCategoryᵒᵖ ⥤ DaggerSSet.{u}) :
    diagramInvolution A ≫ diagramInvolution A = 𝟙 _ := by
  apply NatTrans.ext
  funext n
  exact involution_square (A.obj n)

def diagonalInvolution (A : SimplexCategoryᵒᵖ ⥤ DaggerSSet.{u}) :
    End (diagonalFunctor.obj (underlying A)) :=
  End.of (diagonalFunctor.map (diagramInvolution A))

theorem diagonalInvolution_square (A : SimplexCategoryᵒᵖ ⥤ DaggerSSet.{u}) :
    diagonalInvolution A * diagonalInvolution A = 1 := by
  change diagonalFunctor.map (diagramInvolution A) ≫
    diagonalFunctor.map (diagramInvolution A) = 𝟙 _
  rw [← diagonalFunctor.map_comp, diagramInvolution_square, diagonalFunctor.map_id]

def action (A : SimplexCategoryᵒᵖ ⥤ DaggerSSet.{u}) : Action SSet.{u} C2.{u} :=
  DaggerNativeOriginalC2InvolutionAction.action
    (diagonalInvolution A) (diagonalInvolution_square A)

/-- Keep the whole original natural transformation when forgetting and applying edgewise. -/
def underlyingMap {A B : SimplexCategoryᵒᵖ ⥤ DaggerSSet.{u}} (f : A ⟶ B) :
    underlying A ⟶ underlying B :=
  Functor.whiskerRight (Functor.whiskerRight f DaggerSSet.forget) edgewise

theorem involution_naturality {A B : SimplexCategoryᵒᵖ ⥤ DaggerSSet.{u}} (f : A ⟶ B) :
    diagramInvolution A ≫ underlyingMap f = underlyingMap f ≫ diagramInvolution B := by
  apply NatTrans.ext
  funext n
  exact involution_natural (f.app n)

/-- Every whole original dagger natural transformation gives a strict original-C2 map. -/
def map {A B : SimplexCategoryᵒᵖ ⥤ DaggerSSet.{u}} (f : A ⟶ B) : action A ⟶ action B :=
  DaggerNativeOriginalC2InvolutionAction.map
    (diagonalInvolution A) (diagonalInvolution_square A)
    (diagonalInvolution B) (diagonalInvolution_square B)
    (diagonalFunctor.map (underlyingMap f)) (by
      change diagonalFunctor.map (diagramInvolution A) ≫
          diagonalFunctor.map (underlyingMap f) =
        diagonalFunctor.map (underlyingMap f) ≫ diagonalFunctor.map (diagramInvolution B)
      rw [← diagonalFunctor.map_comp, ← diagonalFunctor.map_comp, involution_naturality])

end
end DaggerNativeRealDaggerDiagramAction
