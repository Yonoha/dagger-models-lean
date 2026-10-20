import OriginalEC2StrictFixedPointInclusion
import TopCatModelCategory.TopCat.HornDeformationRetract
import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex

/-!
# The literal singular equivariant mapping object of original EC₂

This is the point-set compact-open equivariant mapping space already used by
the original strict fixed-point inclusion, followed by the singular functor.
Its Kan property is inherited from the retained singular-set theorem.  No
derived mapping-space recognition is asserted.
-/

set_option autoImplicit false

open CategoryTheory DaggerModels Opposite Simplicial
open DaggerOriginalDaggerRealizationC2Action
open DaggerOriginalDaggerRealizationContinuousAction
open DaggerOriginalEquivariantConstantMaps
open DaggerOriginalEC2RealizationAction

universe u

namespace DaggerOriginalEC2HomotopyFixedPointObject

noncomputable section

/-- The actual equivariant compact-open mapping space from original EC₂. -/
def mappingTop (X : ContAction TopCat.{u} C2.{u}) : TopCat.{u} :=
  TopCat.of (EquivariantMaps realizedEC2ContinuousAction.{u} X)

/-- The literal singular complex of that equivariant mapping space. -/
def mappingSing (X : ContAction TopCat.{u} C2.{u}) : SSet.{u} :=
  TopCat.toSSet.obj (mappingTop X)

/-- The original point-set mapping construction produces a Kan complex. -/
instance mappingSing_kan (X : ContAction TopCat.{u} C2.{u}) :
    SSet.KanComplex (mappingSing X) := by
  unfold mappingSing
  infer_instance

/-- An original vertex gives a zero-simplex in the literal singular
equivariant mapping complex, represented by its canonical constant map. -/
def canonicalZeroSimplex (K : DaggerSSet.{u}) (x : K.toSSet _⦋0⦌) :
    (mappingSing (realizedContinuousActionFunctor.obj K)).obj (op ⦋0⦌) :=
  (TopCat.toSSetObjEquiv
    (mappingTop (realizedContinuousActionFunctor.obj K)) (op ⦋0⦌)).symm
      (ContinuousMap.const _ (canonicalConstantMap
        realizedEC2ContinuousAction.{u} K x))

end

end DaggerOriginalEC2HomotopyFixedPointObject
