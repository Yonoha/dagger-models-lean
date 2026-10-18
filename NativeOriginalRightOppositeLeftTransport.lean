import ActualGeneralRightConeNaturality
import NativeOriginalLeftPathInvolutionAction
import NativeOriginalC2RealizationOpposite

/-! The old right/opposite-left comparison retains both endpoint equations and the outer op. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial
open DaggerActualGeneralRightConeMapping DaggerActualGeneralRightConeKan
open DaggerNativeOppositeLeftMappingSimplex DaggerNativeOriginalLeftPathEndpointTransport
open DaggerOriginalDaggerRealizationC2Action
universe u
namespace DaggerNativeOriginalRightOppositeLeftTransport
noncomputable section

def rightMapTo {X Y : SSet.{u}} (f : X ⟶ Y)
    (x y : X _⦋0⦌) (a b : Y _⦋0⦌)
    (hx : f.app (op ⦋0⦌) x = a) (hy : f.app (op ⦋0⦌) y = b) :
    rightMapping X x y ⟶ rightMapping Y a b := by
  subst a
  subst b
  exact DaggerActualGeneralRightConeMapping.map f x y

theorem rightMapTo_raw {X Y : SSet.{u}} (f : X ⟶ Y)
    (x y : X _⦋0⦌) (a b : Y _⦋0⦌)
    (hx : f.app (op ⦋0⦌) x = a) (hy : f.app (op ⦋0⦌) y = b)
    (n : SimplexCategoryᵒᵖ) (v : (rightMapping X x y).obj n) :
    ((rightMapTo f x y a b hx hy).app n v).val = v.val ≫ f := by
  subst a
  subst b
  rfl

theorem op_vertex {X Y : SSet.{u}} (f : X ⟶ Y)
    (x : X _⦋0⦌) (a : Y _⦋0⦌) (hx : f.app (op ⦋0⦌) x = a) :
    (SSet.opFunctor.map f).app (op ⦋0⦌) (SSet.opObjEquiv.symm x) =
      SSet.opObjEquiv.symm a := hx

def oppositeMapTo {X Y : SSet.{u}} (f : X ⟶ Y)
    (x y : X _⦋0⦌) (a b : Y _⦋0⦌)
    (hx : f.app (op ⦋0⦌) x = a) (hy : f.app (op ⦋0⦌) y = b) :
    oppositeLeft X x y ⟶ oppositeLeft Y a b :=
  SSet.opFunctor.map (leftMapTo (SSet.opFunctor.map f)
    (SSet.opObjEquiv.symm y) (SSet.opObjEquiv.symm x)
    (SSet.opObjEquiv.symm b) (SSet.opObjEquiv.symm a)
    (op_vertex f y b hy) (op_vertex f x a hx))

theorem comparison_naturalityTo {X Y : SSet.{u}} (f : X ⟶ Y)
    (x y : X _⦋0⦌) (a b : Y _⦋0⦌)
    (hx : f.app (op ⦋0⦌) x = a) (hy : f.app (op ⦋0⦌) y = b) :
    rightMapTo f x y a b hx hy ≫ (DaggerActualGeneralRightConeKan.comparisonIso Y a b).hom =
      (DaggerActualGeneralRightConeKan.comparisonIso X x y).hom ≫
        oppositeMapTo f x y a b hx hy := by
  subst a
  subst b
  exact hom_naturality f x y

variable {X : SSet.{u}} (s : X ⟶ X) (hs : s ≫ s = 𝟙 X)
variable (x y : X _⦋0⦌) (hx : s.app (op ⦋0⦌) x = x) (hy : s.app (op ⦋0⦌) y = y)

include hs

theorem opposite_square : SSet.opFunctor.map s ≫ SSet.opFunctor.map s = 𝟙 X.op := by
  rw [← SSet.opFunctor.map_comp, hs, SSet.opFunctor.map_id]

def innerLeftAction : Action SSet.{u} C2.{u} :=
  DaggerNativeOriginalLeftPathInvolutionAction.leftAction (SSet.opFunctor.map s)
    (opposite_square s hs) (SSet.opObjEquiv.symm y) (SSet.opObjEquiv.symm x)
    (op_vertex s y y hy) (op_vertex s x x hx)

def oppositeLeftAction : Action SSet.{u} C2.{u} :=
  DaggerNativeOriginalC2RealizationOpposite.oppositeFunctor.obj (innerLeftAction s hs x y hx hy)

theorem oppositeLeftAction_generator :
    ((oppositeLeftAction s hs x y hx hy).ρ generator).asHom =
      oppositeMapTo s x y x y hx hy := by
  change SSet.opFunctor.map
    (((innerLeftAction s hs x y hx hy).ρ generator).asHom) = _
  unfold innerLeftAction DaggerNativeOriginalLeftPathInvolutionAction.leftAction
  rw [DaggerNativeOriginalC2InvolutionAction.action_generator]
  rfl

end
end DaggerNativeOriginalRightOppositeLeftTransport
