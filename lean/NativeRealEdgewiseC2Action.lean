import NativeRealEdgewiseDaggerInvolution
import NativeOriginalC2InvolutionAction

/-! The ORIGINAL edgewise dagger as an action of the UNCHANGED original C2.
The entire functor and each actual constant-vertex map are retained.
-/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial DaggerModels
open DaggerNativeRealEdgewiseSSet DaggerNativeRealEdgewiseDaggerInvolution
open DaggerOriginalDaggerRealizationC2Action DaggerOriginalCompletedDaggerMappingAction
universe u
namespace DaggerNativeRealEdgewiseC2Action
noncomputable section

def involutionEnd (X : DaggerSSet.{u}) : End (edgewise.obj X.toSSet) := End.of (involution X)

theorem involutionEnd_square (X : DaggerSSet.{u}) :
    involutionEnd X * involutionEnd X = 1 := involution_square X

def action (X : DaggerSSet.{u}) : Action SSet.{u} C2.{u} :=
  DaggerNativeOriginalC2InvolutionAction.action (involutionEnd X) (involutionEnd_square X)

theorem action_generator (X : DaggerSSet.{u}) :
    ((action X).ρ generator).asHom = involution X :=
  DaggerNativeOriginalC2InvolutionAction.action_generator (involutionEnd X) (involutionEnd_square X)

def map {X Y : DaggerSSet.{u}} (f : X ⟶ Y) : action X ⟶ action Y :=
  DaggerNativeOriginalC2InvolutionAction.map (involutionEnd X) (involutionEnd_square X)
    (involutionEnd Y) (involutionEnd_square Y) (edgewise.map f.hom) (involution_natural f)

def functor : DaggerSSet.{u} ⥤ Action SSet.{u} C2.{u} where
  obj := action
  map f := map f
  map_id X := by
    apply Action.hom_ext
    exact edgewise.map_id X.toSSet
  map_comp f g := by
    apply Action.hom_ext
    exact edgewise.map_comp f.hom g.hom

theorem map_hom {X Y : DaggerSSet.{u}} (f : X ⟶ Y) :
    (map f).hom = edgewise.map f.hom := rfl

theorem generator_degree (X : DaggerSSet.{u}) (n : SimplexCategoryᵒᵖ) :
    (((action X).ρ generator).asHom).app n =
      X.dagger.app (DaggerNativeRealEdgewiseIndex.epsilon.op.obj n) := by
  rw [action_generator]
  rfl

theorem generator_fixed_vertex (X : DaggerSSet.{u}) (x : X.toSSet.obj (op ⦋0⦌)) :
    (((action X).ρ generator).asHom).app (op ⦋0⦌) (X.toSSet.σ (0 : Fin 1) x) =
      X.toSSet.σ (0 : Fin 1) x := by
  rw [action_generator]
  exact involution_degenerate_vertex X x

def fixedVertexMap (X : DaggerSSet.{u}) (x : X.toSSet.obj (op ⦋0⦌)) :
    Action.trivial C2.{u} (Δ[0] : SSet.{u}) ⟶ action X where
  hom := vertexMap X x
  comm g := by
    rcases originalC2_cases g with rfl | rfl
    · simp
    · change (𝟙 (Δ[0] : SSet.{u})) ≫ vertexMap X x =
        vertexMap X x ≫ ((action X).ρ generator).asHom
      rw [Category.id_comp, action_generator]
      exact (vertexMap_fixed X x).symm

theorem fixedVertexMap_hom (X : DaggerSSet.{u}) (x : X.toSSet.obj (op ⦋0⦌)) :
    (fixedVertexMap X x).hom = vertexMap X x := rfl

end
end DaggerNativeRealEdgewiseC2Action
