import DaggerModels.UnitaryObstruction
import Mathlib.CategoryTheory.Category.ULift
import Mathlib.CategoryTheory.CodiscreteCategory

set_option autoImplicit false

open CategoryTheory DaggerModels

universe u

namespace DaggerModels.OriginalWalkingIsoIntegerObstruction

/-- The ordinary walking isomorphism, with objects and Homs both in universe `u`. -/
abbrev walkingIso : Type u := AsSmall.{u} (Codiscrete Bool)

def walkingZero : walkingIso.{u} := ⟨⟨false⟩⟩

def walkingOne : walkingIso.{u} := ⟨⟨true⟩⟩

def walkingForward : walkingZero.{u} ⟶ walkingOne.{u} := ⟨⟨⟩⟩

def walkingBackward : walkingOne.{u} ⟶ walkingZero.{u} := ⟨⟨⟩⟩

/-- The generator is an ordinary isomorphism, with no dagger imposed on it. -/
def walkingForwardIso : walkingZero.{u} ≅ walkingOne.{u} where
  hom := walkingForward
  inv := walkingBackward
  hom_inv_id := rfl
  inv_hom_id := rfl

/-- The actual integer dagger groupoid, lifting both its objects and its Hom types. -/
abbrev integerTarget : Type u := AsSmall.{u} UnitaryObstruction.IntegerGroupoid

def integerZero : integerTarget.{u} := ⟨UnitaryObstruction.IntegerGroupoid.zero⟩

def integerOne : integerTarget.{u} := ⟨UnitaryObstruction.IntegerGroupoid.one⟩

/-- The lifted dagger is exactly the existing integer-groupoid dagger downstairs. -/
instance integerDaggerCategory : DaggerCategory integerTarget.{u} where
  dagger f := ⟨dagger f.down⟩
  dagger_involutive f := by
    apply ULift.ext
    exact DaggerCategory.dagger_involutive f.down
  dagger_id X := by
    apply ULift.ext
    exact DaggerCategory.dagger_id (ULift.down X)
  dagger_comp f g := by
    apply ULift.ext
    exact DaggerCategory.dagger_comp f.down g.down

/-- Forgetting the lift preserves the actual dagger, not only ordinary composition. -/
instance integerDownDaggerFunctor :
    DaggerFunctor (AsSmall.down : integerTarget.{u} ⥤
      UnitaryObstruction.IntegerGroupoid) where
  map_dagger _ := rfl

/-- The ordinary walking isomorphism maps to the zero-labelled ordinary isomorphism. -/
def baseFunctor : Codiscrete Bool ⥤ UnitaryObstruction.IntegerGroupoid where
  obj x := (show UnitaryObstruction.IntegerGroupoid from x.as)
  map _ := (0 : ℤ)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Both source and target use the same `AsSmall.{u}` universe lift. -/
def walkingToInteger : walkingIso.{u} ⥤ integerTarget.{u} :=
  AsSmall.down ⋙ baseFunctor ⋙ AsSmall.up

@[simp] theorem walkingToInteger_zero :
    walkingToInteger.{u}.obj walkingZero = integerZero := rfl

@[simp] theorem walkingToInteger_one :
    walkingToInteger.{u}.obj walkingOne = integerOne := rfl

theorem walkingToInteger_forward_down :
    ((walkingToInteger.{u}.map walkingForward).down :
      UnitaryObstruction.IntegerGroupoid.zero ⟶
        UnitaryObstruction.IntegerGroupoid.one) = (0 : ℤ) := rfl

/-- The old no-unitary obstruction transports through the dagger-preserving down functor. -/
theorem integer_noUnitary (f : integerZero.{u} ⟶ integerOne.{u}) :
    ¬ IsUnitary f := by
  intro hf
  have hu := map_isUnitary
    (AsSmall.down : integerTarget.{u} ⥤ UnitaryObstruction.IntegerGroupoid) hf
  exact UnitaryObstruction.no_unitary_false_true _ hu

/-- The image of the ordinary walking isomorphism is not a unitary isomorphism. -/
theorem walkingForward_image_notUnitary :
    ¬ IsUnitary (walkingToInteger.{u}.map walkingForward) :=
  integer_noUnitary _

end DaggerModels.OriginalWalkingIsoIntegerObstruction
