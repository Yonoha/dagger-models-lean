import NativeWalkingHomotopyNaturalIso

/-!
# Original walking cylinders on actual internal Hom objects

Transpose evaluation against a whole original J-cylinder. The endpoints are
precisely Mathlib's MonoidalClosed.pre maps, without a new internal Hom model.
-/
set_option autoImplicit false
open CategoryTheory MonoidalCategory CartesianMonoidalCategory DaggerModels
open DaggerActualFreeWalkingIsoIntegerObstruction
open DaggerActualFreeAntiWalkingCategoricalCylinder
open scoped MonoidalClosed
universe u
namespace DaggerNativeWalkingInternalHomCylinder
noncomputable section

def evaluationShuffle {X Y : SSet.{u}} (H : X ⊗ J ⟶ Y) (Z : SSet.{u}) :
    X ⊗ (((ihom Y).obj Z) ⊗ J) ⟶ Y ⊗ ((ihom Y).obj Z) :=
  lift
    (lift (fst X (((ihom Y).obj Z) ⊗ J))
      (snd X (((ihom Y).obj Z) ⊗ J) ≫ snd ((ihom Y).obj Z) J) ≫ H)
    (snd X (((ihom Y).obj Z) ⊗ J) ≫ fst ((ihom Y).obj Z) J)

theorem evaluationShuffle_endpoint {X Y : SSet.{u}} (H : X ⊗ J ⟶ Y)
    (Z : SSet.{u}) (b : Bool) (f : X ⟶ Y)
    (hf : intervalEndpoint X b ≫ H = f) :
    X ◁ intervalEndpoint ((ihom Y).obj Z) b ≫ evaluationShuffle H Z = f ▷ ((ihom Y).obj Z) := by
  apply NatTrans.ext
  funext n t
  rcases t with ⟨x, z⟩
  change (((intervalEndpoint X b ≫ H).app n x), z) = (f.app n x, z)
  rw [hf]

def preCylinder {X Y : SSet.{u}} (H : X ⊗ J ⟶ Y) (Z : SSet.{u}) :
    ((ihom Y).obj Z) ⊗ J ⟶ (ihom X).obj Z :=
  MonoidalClosed.curry (evaluationShuffle H Z ≫ (ihom.ev Y).app Z)

/-- Both transposed endpoints are the unchanged actual precomposition maps. -/
theorem preCylinder_endpoint {X Y : SSet.{u}} (H : X ⊗ J ⟶ Y)
    (Z : SSet.{u}) (b : Bool) (f : X ⟶ Y)
    (hf : intervalEndpoint X b ≫ H = f) :
    intervalEndpoint ((ihom Y).obj Z) b ≫ preCylinder H Z = (MonoidalClosed.pre f).app Z := by
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_natural_left, preCylinder, MonoidalClosed.uncurry_curry,
    MonoidalClosed.uncurry_pre, ← Category.assoc, evaluationShuffle_endpoint H Z b f hf]

end
end DaggerNativeWalkingInternalHomCylinder
