import DaggerModels.DaggerGraphPresheaf

/-!
# Limits, colimits, and presentability of dagger simplicial graphs

These properties are transported along the actual graph-presheaf equivalence.
The value, diagram, and presentability cardinal universes are all the arbitrary
common universe `u`. This does not yet prove presentability of dagger simplicial
categories or finitarity of their word monad.
-/

open CategoryTheory Limits

universe u

namespace DaggerModels

/-- The original dagger graph category admits all `u`-small limits. -/
theorem daggerGraphHasLimits : HasLimits DaggerSimplicialGraph.{u} :=
  Adjunction.has_limits_of_equivalence daggerGraphEquivalencePresheaf.functor

/-- The original dagger graph category admits all `u`-small colimits. -/
theorem daggerGraphHasColimits : HasColimits DaggerSimplicialGraph.{u} :=
  Adjunction.has_colimits_of_equivalence daggerGraphEquivalencePresheaf.functor

/-- Graph local finite presentability used in the proof of `bg.lem.presentable`. -/
theorem daggerGraphLocallyFinitelyPresentable :
    IsLocallyFinitelyPresentable.{u} DaggerSimplicialGraph.{u} := by
  let : IsLocallyFinitelyPresentable.{u} (DaggerGraphIndex.Objᵒᵖ ⥤ Type u) :=
    DaggerGraphIndex.presheavesLocallyFinitelyPresentable
  let : Fact (Cardinal.aleph0.{u}).IsRegular := Cardinal.fact_isRegular_aleph0
  exact daggerGraphEquivalencePresheaf.symm.isCardinalLocallyPresentable Cardinal.aleph0

/-- Dagger graphs are locally presentable at their value universe. -/
theorem daggerGraphLocallyPresentable : IsLocallyPresentable.{u} DaggerSimplicialGraph.{u} := by
  let : Fact (Cardinal.aleph0.{u}).IsRegular := Cardinal.fact_isRegular_aleph0
  exact ⟨Cardinal.aleph0, inferInstance, daggerGraphLocallyFinitelyPresentable⟩

end DaggerModels
