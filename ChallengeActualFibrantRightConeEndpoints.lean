import ActualFibrantGadgetData
import OriginalCounitRightCone

/-! The selected endpoints are the literal C(unit) images of the original pushout-cone endpoints. -/
set_option autoImplicit false
open CategoryTheory Opposite MonoidalCategory CartesianMonoidalCategory
open DaggerModels OrdinaryRigidification DaggerOriginalCounitRightCone
universe u
namespace DaggerActualFibrantRightConeEndpointsChallenge

def statement : Prop :=
  ∀ n : ℕ,
    SSet.KanComplex.W (TopCat.toSSet.map (SSet.toTop.map
      (toUnit
        ((rigidification.map (DaggerActualFibrantGadgetData.unit.app (cone.{u} n))).obj
            (alphaObj n) ⟶[SSet.{u}]
          (rigidification.map (DaggerActualFibrantGadgetData.unit.app (cone.{u} n))).obj
            (omegaObj n)))))

end DaggerActualFibrantRightConeEndpointsChallenge
