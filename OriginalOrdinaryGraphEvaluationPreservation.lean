import OriginalOrdinaryGraphColimitEvaluation

/-!
# Preservation by original ordinary graph evaluations

The original graph colimit and its already proved vertex and total-edge
universal properties give the standard Mathlib preservation interfaces.
No filtered hypothesis is needed for these evaluations.
-/

open CategoryTheory Limits

universe u

namespace DaggerModels.OriginalOrdinaryGraphEvaluation

/-- Original vertices with their original maps, valued in Type. -/
def vertices : SimplicialGraph.{u} ⥤ Type u where
  obj G := G.Obj
  map k := k.obj

/-- The original vertex evaluation preserves every u-small diagram's colimit. -/
theorem vertices_preservesColimit {J : Type u} [SmallCategory J]
    (F : J ⥤ SimplicialGraph.{u}) : PreservesColimit F vertices :=
  preservesColimit_of_preserves_colimit_cocone
    (SimplicialGraph.TotalSpace.Colimit.isColimit F)
    (SimplicialGraph.TotalSpace.Colimit.objectIsColimit F)

/-- The original total-edge evaluation preserves every u-small colimit. -/
theorem edgeFunctor_preservesColimit {J : Type u} [SmallCategory J]
    (F : J ⥤ SimplicialGraph.{u}) :
    PreservesColimit F SimplicialGraph.TotalSpace.edgeFunctor :=
  preservesColimit_of_preserves_colimit_cocone
    (SimplicialGraph.TotalSpace.Colimit.isColimit F)
    (SimplicialGraph.TotalSpace.Colimit.totalEdgeIsColimit F)

/-- Vertex evaluation preserves colimits with objects and arrows in universe u. -/
theorem vertices_preservesColimits : PreservesColimitsOfSize.{u, u} vertices.{u} where
  preservesColimitsOfShape :=
    { preservesColimit := fun {F} ↦ vertices_preservesColimit F }

/-- Total-edge evaluation preserves colimits at the same universe. -/
theorem edgeFunctor_preservesColimits :
    PreservesColimitsOfSize.{u, u} SimplicialGraph.TotalSpace.edgeFunctor.{u} where
  preservesColimitsOfShape :=
    { preservesColimit := fun {F} ↦ edgeFunctor_preservesColimit F }

end DaggerModels.OriginalOrdinaryGraphEvaluation
