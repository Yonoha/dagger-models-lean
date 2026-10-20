import OriginalEC2RealizationAction
import OriginalEC2RealizationContractibility
import OriginalEquivariantConstantMaps

/-!
# Strict fixed points as actual EC₂-equivariant constant maps

The domain is the literal fixed-point subtype of an arbitrary continuous
`C₂`-action. The codomain has the subspace compact-open topology on maps
from the already constructed actual realized `EC₂`.
-/

set_option autoImplicit false

open CategoryTheory DaggerModels
open DaggerOriginalDaggerRealizationC2Action
open DaggerOriginalEquivariantConstantMaps
open DaggerOriginalEC2RealizationAction
open DaggerOriginalEC2RealizationContractibility

universe u

namespace DaggerOriginalEC2StrictFixedPointInclusion

noncomputable section

/-- The continuous constant-map inclusion for the literal realized `EC₂`. -/
def strictToEquivariantMaps (X : ContAction TopCat.{u} C2.{u}) :
    C(FixedPoints X, EquivariantMaps realizedEC2ContinuousAction.{u} X) :=
  ⟨constantMap realizedEC2ContinuousAction.{u} X,
    constantMap_continuous realizedEC2ContinuousAction.{u} X⟩

/-- Every value of the resulting map is the original strict fixed point. -/
theorem strictToEquivariantMaps_apply (X : ContAction TopCat.{u} C2.{u})
    (x : FixedPoints X) (e : realizedEC2ContinuousAction.{u}.obj.V) :
    (strictToEquivariantMaps X x).val e = x.val :=
  constantMap_apply realizedEC2ContinuousAction.{u} X x e

/-- Evaluation at the actual identity-labelled point of `EC₂`. -/
theorem strictToEquivariantMaps_realizedPoint
    (X : ContAction TopCat.{u} C2.{u}) (x : FixedPoints X) :
    (strictToEquivariantMaps X x).val realizedPoint.{u} = x.val :=
  strictToEquivariantMaps_apply X x realizedPoint.{u}

/-- A constant equivariant map remembers its unique strict fixed-point value. -/
theorem strictToEquivariantMaps_injective (X : ContAction TopCat.{u} C2.{u}) :
    Function.Injective (strictToEquivariantMaps X) := by
  intro x y h
  apply Subtype.ext
  calc
    x.val = (strictToEquivariantMaps X x).val realizedPoint.{u} :=
      (strictToEquivariantMaps_realizedPoint X x).symm
    _ = (strictToEquivariantMaps X y).val realizedPoint.{u} :=
      congrArg
        (fun f : EquivariantMaps realizedEC2ContinuousAction.{u} X ↦
          f.val realizedPoint.{u}) h
    _ = y.val := strictToEquivariantMaps_realizedPoint X y

end

end DaggerOriginalEC2StrictFixedPointInclusion
