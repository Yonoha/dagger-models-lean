import OriginalOrdinaryFilteredEnrichedColimitUP
import Mathlib.CategoryTheory.Limits.Preserves.Filtered

/-!
# Comparison with the existing semantic ordinary colimit

The original filtered enriched cocone and the existing semantic cocone are
colimits of the same diagram.  Their canonical enriched comparison is an
isomorphism.  Forgetting it transports the already proved original graph
colimit to the graph underlying the semantic cocone for this diagram.
-/

open CategoryTheory Limits

universe u

namespace DaggerModels.OriginalOrdinaryFilteredEnrichedPoint

open OriginalOrdinaryComposableEdges

variable {J : Type u} [SmallCategory J] [IsFiltered J]
variable (K : J ⥤ SimplicialCat.{u, u})

/-- Canonical comparison from the original filtered point to the semantic colimit. -/
noncomputable def semanticComparison :
    point K ≅ SimplicialCat.SemanticColimit.point K :=
  IsColimit.coconePointUniqueUpToIso (isColimit K)
    (SimplicialCat.SemanticColimit.isColimit K)

/-- The comparison commutes with every original enriched leg. -/
theorem leg_semanticComparison (j : J) :
    leg K j ≫ (semanticComparison K).hom =
      SimplicialCat.SemanticColimit.leg K j :=
  IsColimit.comp_coconePointUniqueUpToIso_hom (isColimit K)
    (SimplicialCat.SemanticColimit.isColimit K) j

/-- The graph underlying the existing semantic cocone is colimiting for this
filtered original diagram. -/
noncomputable def semanticGraphIsColimit :
    IsColimit (SimplicialCat.graphForget.mapCocone
      (SimplicialCat.SemanticColimit.cocone K)) := by
  have hgraph : IsColimit (SimplicialCat.graphForget.mapCocone (cocone K)) := by
    rw [cocone_graph K]
    exact SimplicialGraph.TotalSpace.Colimit.isColimit (graphDiagram K)
  let φ : SimplicialCat.graphForget.mapCocone (cocone K) ≅
      SimplicialCat.graphForget.mapCocone
        (SimplicialCat.SemanticColimit.cocone K) :=
    Cocones.ext (SimplicialCat.graphForget.mapIso (semanticComparison K)) (by
      intro j
      change SimplicialCat.graphForget.map (leg K j) ≫
          SimplicialCat.graphForget.map (semanticComparison K).hom =
        SimplicialCat.graphForget.map
          (SimplicialCat.SemanticColimit.leg K j)
      rw [← Functor.map_comp, leg_semanticComparison])
  exact hgraph.ofIsoColimit φ

/-- The graph forgetful functor preserves this original filtered colimit. -/
theorem graphForget_preservesColimit :
    PreservesColimit K SimplicialCat.graphForget :=
  preservesColimit_of_preserves_colimit_cocone (isColimit K) (by
    rw [cocone_graph K]
    exact SimplicialGraph.TotalSpace.Colimit.isColimit (graphDiagram K))

/-- At the same object and morphism universe, graph forgetting preserves all
filtered ordinary simplicial-category colimits. -/
instance graphForget_preservesFilteredColimitsOfSize :
    PreservesFilteredColimitsOfSize.{u, u} SimplicialCat.graphForget.{u} where
  preserves_filtered_colimits _ _ _ :=
    { preservesColimit := fun {K} ↦ graphForget_preservesColimit K }

end DaggerModels.OriginalOrdinaryFilteredEnrichedPoint
