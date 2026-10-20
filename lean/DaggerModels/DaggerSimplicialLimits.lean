import DaggerModels.DaggerSimplicialMonadicity
import DaggerModels.DaggerGraphPresentable
import Mathlib.CategoryTheory.Monad.Limits

/-!
# Limits over dagger simplicial graphs

The actual graph forgetful functor creates limits by its proved monadicity.
Graph completeness therefore supplies all limits in the common value universe.
This is not the different forgetful functor to ordinary simplicial categories
in Part I `bg.lem.creation`.
-/

open CategoryTheory Limits

universe u w w'

namespace DaggerModels.DaggerSimplicialCat

/-- The actual graph forgetful functor creates limits at arbitrary diagram sizes. -/
noncomputable def forgetGraphCreatesLimits :
    CreatesLimitsOfSize.{w, w'} forgetGraph.{u} :=
  monadicCreatesLimits forgetGraph

/-- In particular, the graph forgetful functor creates all `u`-small limits. -/
noncomputable def forgetGraphCreatesSmallLimits : CreatesLimits forgetGraph.{u} :=
  forgetGraphCreatesLimits

/-- Dagger simplicial categories admit limits of all `u`-small diagrams. -/
theorem daggerSimplicialHasLimits : HasLimits DaggerSimplicialCat.{u, u} := by
  letI : HasLimits DaggerSimplicialGraph.{u} := daggerGraphHasLimits
  letI : CreatesLimits forgetGraph.{u} := forgetGraphCreatesSmallLimits
  exact hasLimits_of_hasLimits_createsLimits forgetGraph

/-- The graph forgetful functor preserves all `u`-small limits. -/
theorem forgetGraphPreservesLimits : PreservesLimitsOfSize.{u, u} forgetGraph.{u} := by
  letI : HasLimits DaggerSimplicialGraph.{u} := daggerGraphHasLimits
  letI : CreatesLimits forgetGraph.{u} := forgetGraphCreatesSmallLimits
  infer_instance

/-- Creation also reflects limiting cones at arbitrary diagram sizes. -/
theorem forgetGraphReflectsLimits : ReflectsLimitsOfSize.{w, w'} forgetGraph.{u} := by
  letI : CreatesLimitsOfSize.{w, w'} forgetGraph.{u} := forgetGraphCreatesLimits
  infer_instance

end DaggerModels.DaggerSimplicialCat
