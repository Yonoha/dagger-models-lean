import DaggerModels.DaggerOrdinaryColimitCreation
import DaggerModels.DaggerOrdinaryLimitCreation

/-! Part I `bg.lem.creation`: the actual ordinary forgetful functor creates
limits and colimits, with no existence assumption or restriction on object maps.
All four object, hom, and diagram universes remain independent. -/

open CategoryTheory Limits

universe o v w w'

namespace DaggerModels.DaggerSimplicialCat

theorem forget_createsLimits : Nonempty (CreatesLimitsOfSize.{w', w} forget.{o, v}) :=
  ⟨OrdinaryLimitCreation.forgetCreatesLimitsOfSize⟩

theorem forget_createsColimits : Nonempty (CreatesColimitsOfSize.{w', w} forget.{o, v}) :=
  ⟨OrdinaryColimit.forgetCreatesColimits⟩

end DaggerModels.DaggerSimplicialCat
