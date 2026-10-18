import OriginalDaggerRealizationVertices
import Mathlib.CategoryTheory.Action.Basic
import Mathlib.Algebra.Group.ULift
import Mathlib.Data.ZMod.Basic

/-!
# The actual realized dagger as a C₂-action

The action is on the original topological realization. It is a categorical
`Action TopCat`; no homotopy-fixed-point or continuous-group-action model is
asserted here.
-/

set_option autoImplicit false

open CategoryTheory DaggerModels Opposite Simplicial
open DaggerOriginalDaggerRealizationInvolution
open DaggerOriginalDaggerRealizationVertices

universe u

namespace DaggerOriginalDaggerRealizationC2Action

noncomputable section

private abbrev R : SSet.{u} ⥤ TopCat.{u} := SSet.toTop.{u}

/-- The two-element group, lifted into the same universe as the realization. -/
abbrev C2 : Type u := ULift.{u} (Multiplicative (ZMod 2))

/-- The nonidentity element of the actual lifted two-element group. -/
def generator : C2.{u} := ULift.up (Multiplicative.ofAdd (1 : ZMod 2))

private theorem generator_ne_one : generator.{u} ≠ 1 := by decide

private theorem generator_mul_self : generator.{u} * generator = 1 := by decide

private theorem c2_cases (g : C2.{u}) : g = 1 ∨ g = generator := by
  have hz : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  rcases hz (Multiplicative.toAdd g.down) with h | h
  · left
    apply ULift.down_injective
    exact h
  · right
    apply ULift.down_injective
    exact h

/-- The generator acts by the already proved realized dagger involution. -/
def actionEnd (X : DaggerSSet.{u}) : C2.{u} →*
    End (R.obj X.toSSet) where
  toFun g := if g = 1 then 1 else End.of (realizationInvolutionHom X)
  map_one' := by simp
  map_mul' g h := by
    rcases c2_cases g with rfl | rfl
    · simp
    rcases c2_cases h with rfl | rfl
    · simp
    simp [generator_mul_self, generator_ne_one, End.mul_def,
      realizationInvolution_sq]

/-- The distinguished element acts by the literal original realized map. -/
theorem actionEnd_generator (X : DaggerSSet.{u}) :
    actionEnd X generator = realizationInvolutionHom X := by
  simp [actionEnd, generator_ne_one]

/-- The actual realization, with its categorical two-element action. -/
def realizedAction (X : DaggerSSet.{u}) : Action TopCat.{u} C2.{u} where
  V := R.obj X.toSSet
  ρ := actionEnd X

/-- The action generator is the previously constructed topological involution. -/
theorem realizedAction_generator (X : DaggerSSet.{u}) :
    (realizedAction X).ρ generator = realizationInvolutionHom X :=
  actionEnd_generator X

/-- Original dagger maps induce equivariant maps of actual realizations. -/
def realizedActionFunctor : DaggerSSet.{u} ⥤ Action TopCat.{u} C2.{u} where
  obj := realizedAction
  map := fun {X Y} f ↦
    { hom := R.map f.hom
      comm := by
        intro g
        change actionEnd X g ≫ R.map f.hom =
          R.map f.hom ≫ actionEnd Y g
        rcases c2_cases g with rfl | rfl
        · simp
        · simpa only [actionEnd_generator] using realizationInvolution_naturality f }
  map_id X := by
    apply Action.hom_ext
    change R.map (𝟙 X.toSSet) = 𝟙 (R.obj X.toSSet)
    exact R.map_id _
  map_comp f g := by
    apply Action.hom_ext
    change R.map (f.hom ≫ g.hom) = R.map f.hom ≫ R.map g.hom
    exact R.map_comp _ _

/-- The underlying object remains the original realization. -/
theorem realizedActionFunctor_obj (X : DaggerSSet.{u}) :
    (realizedActionFunctor.obj X).V = R.obj X.toSSet := rfl

/-- The underlying map remains the realization of the original dagger map. -/
theorem realizedActionFunctor_map {X Y : DaggerSSet.{u}} (f : X ⟶ Y) :
    (realizedActionFunctor.map f).hom = R.map f.hom := rfl

/-- Every group element fixes each realized original vertex. -/
theorem realizedVertex_action_fixed (X : DaggerSSet.{u})
    (x : X.toSSet _⦋0⦌) (g : C2.{u}) :
    ((realizedActionFunctor.obj X).ρ g).asHom
      (realizedVertex X x) = realizedVertex X x := by
  change (actionEnd X g).asHom (realizedVertex X x) = realizedVertex X x
  rcases c2_cases g with rfl | rfl
  · simp [End.asHom]
  · simpa only [actionEnd_generator, End.asHom] using realizedVertex_fixed X x

end

end DaggerOriginalDaggerRealizationC2Action
