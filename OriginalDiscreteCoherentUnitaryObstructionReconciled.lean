import OriginalUnitaryDiscreteRecovered
import DaggerModels.UnitaryObstruction

set_option autoImplicit false

open CategoryTheory HomotopicalAlgebra Simplicial DaggerModels

universe u

namespace DaggerModels.OriginalDiscreteCoherentUnitaryObstruction

open DaggerUnitaryInvariance DaggerUnitaryDiscrete

/-- A discrete dagger target with no strict unitary between two objects has no coherent
unitary class between those same objects, for the original replacement parameter. -/
theorem noCoherentUnitaryOfNoUnitary (A : Type u) [Category.{u} A]
    [DaggerCategory A] (R : FunctorialFibrantReplacement.{u}) (x y : A)
    (h : ∀ a : x ⟶ y, ¬ IsUnitary a)
    (z : SSet.π₀ ((ordinaryEnrichment A).enriched.Hom x y)) :
    ¬ CoherentlyUnitary R (ordinaryEnrichment A) x y z := by
  intro hz
  have hu := (coherentlyUnitary_iff_unitary A x y R z).1 hz
  exact h _ hu

/-- The existing integer groupoid supplies the actual two endpoint contradiction at
universe zero. A universe-lifted target is still needed for the all-`u` generator map. -/
theorem integerGroupoid_noCoherentUnitary
    (R : FunctorialFibrantReplacement.{0})
    (z : SSet.π₀
      ((ordinaryEnrichment UnitaryObstruction.IntegerGroupoid).enriched.Hom
        UnitaryObstruction.IntegerGroupoid.zero
        UnitaryObstruction.IntegerGroupoid.one)) :
    ¬ CoherentlyUnitary R
      (ordinaryEnrichment UnitaryObstruction.IntegerGroupoid)
      UnitaryObstruction.IntegerGroupoid.zero
      UnitaryObstruction.IntegerGroupoid.one z :=
  noCoherentUnitaryOfNoUnitary UnitaryObstruction.IntegerGroupoid R
    UnitaryObstruction.IntegerGroupoid.zero
    UnitaryObstruction.IntegerGroupoid.one
    UnitaryObstruction.no_unitary_false_true z

end DaggerModels.OriginalDiscreteCoherentUnitaryObstruction
