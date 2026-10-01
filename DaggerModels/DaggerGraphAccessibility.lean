import DaggerModels.DaggerGraphEvaluation

/-!
# Detecting accessibility by graph evaluations

The vertex evaluation and every total-edge evaluation jointly detect
accessibility, using the actual dagger graph presheaf equivalence.
-/

open CategoryTheory Limits Opposite

universe u v w

namespace DaggerModels.DaggerGraphEvaluation

attribute [local instance] Cardinal.fact_isRegular_aleph0

/-- The full presheaf equivalence makes the graph evaluations jointly detect accessibility. -/
theorem isCardinalAccessible_of_evaluations {C : Type v} [Category.{w} C]
    (T : C ⥤ DaggerSimplicialGraph.{u})
    [(T ⋙ vertices).IsCardinalAccessible Cardinal.aleph0.{u}]
    [∀ n, (T ⋙ edges n).IsCardinalAccessible Cardinal.aleph0.{u}] :
    T.IsCardinalAccessible Cardinal.aleph0.{u} where
  preservesColimitOfShape {J _ _} := by
    letI : PreservesColimitsOfShape J (T ⋙ daggerGraphEquivalencePresheaf.functor) :=
      preservesColimitsOfShape_of_evaluation _ _ (by
        intro X
        cases X using Opposite.rec
        rename_i X
        cases X with
        | vertex =>
          exact Functor.preservesColimitsOfShape_of_isCardinalAccessible
            (T ⋙ vertices) Cardinal.aleph0 J
        | edge n =>
          exact Functor.preservesColimitsOfShape_of_isCardinalAccessible
            (T ⋙ edges (op n)) Cardinal.aleph0 J)
    exact preservesColimitsOfShape_of_reflects_of_preserves
      T daggerGraphEquivalencePresheaf.functor

end DaggerModels.DaggerGraphEvaluation
