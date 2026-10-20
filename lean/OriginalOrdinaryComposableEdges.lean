import OriginalOrdinaryGraphColimitEvaluation
import OriginalFilteredPullbackColimit
import DaggerModels.SimplicialColimitsFree

/-!
# Composable original edges in a filtered ordinary simplicial-category diagram

The actual ordinary graph forgetful functor supplies vertices and total
simplicial edges.  The literal middle-endpoint pullback is colimiting by the
generic filtered Type pullback theorem.  No composition is defined here.
-/

open CategoryTheory Limits

universe u

namespace DaggerModels.OriginalOrdinaryComposableEdges

variable {J : Type u} [SmallCategory J]
variable (K : J ⥤ SimplicialCat.{u, u})

/-- The existing ordinary graph forgetful functor on the original diagram. -/
def graphDiagram : J ⥤ SimplicialGraph.{u} := K ⋙ SimplicialCat.graphForget

/-- Original total edges in one simplex degree, with their original endpoints. -/
def edgeDegreeDiagram (n : SimplexCategoryᵒᵖ) : J ⥤ Type u :=
  SimplicialGraph.TotalSpace.Colimit.degreeDiagram (graphDiagram K) n

/-- Source endpoint of each original edge in a fixed simplex degree. -/
def edgeSource (n : SimplexCategoryᵒᵖ) :
    edgeDegreeDiagram K n ⟶
      SimplicialGraph.TotalSpace.Colimit.objectDiagram (graphDiagram K) where
  app j e := e.1
  naturality := by
    intro i j α
    funext e
    rfl

/-- Target endpoint of each original edge in a fixed simplex degree. -/
def edgeTarget (n : SimplexCategoryᵒᵖ) :
    edgeDegreeDiagram K n ⟶
      SimplicialGraph.TotalSpace.Colimit.objectDiagram (graphDiagram K) where
  app j e := e.2.1
  naturality := by
    intro i j α
    funext e
    rfl

/-- The actual degreewise total-edge cocone of the graph colimit. -/
noncomputable def edgeCocone (n : SimplexCategoryᵒᵖ) : Cocone (edgeDegreeDiagram K n) :=
  ((evaluation SimplexCategoryᵒᵖ (Type u)).obj n).mapCocone
    (SimplicialGraph.TotalSpace.edgeFunctor.mapCocone
      (SimplicialGraph.TotalSpace.Colimit.cocone (graphDiagram K)))

/-- The actual vertex cocone of the graph colimit. -/
noncomputable def objectCocone :
    Cocone (SimplicialGraph.TotalSpace.Colimit.objectDiagram (graphDiagram K)) :=
  SimplicialGraph.TotalSpace.Colimit.objectCocone (graphDiagram K)
    (SimplicialGraph.TotalSpace.Colimit.cocone (graphDiagram K))

/-- Target endpoint of a total edge in the assembled graph point. -/
noncomputable def pointTarget (n : SimplexCategoryᵒᵖ) :
    (edgeCocone K n).pt ⟶ (objectCocone K).pt := fun e ↦ e.2.1

/-- Source endpoint of a total edge in the assembled graph point. -/
noncomputable def pointSource (n : SimplexCategoryᵒᵖ) :
    (edgeCocone K n).pt ⟶ (objectCocone K).pt := fun e ↦ e.1

/-- The target endpoint commutes with each original total-edge injection. -/
theorem target_compat (n : SimplexCategoryᵒᵖ) (j : J) :
    (edgeCocone K n).ι.app j ≫ pointTarget K n =
      (edgeTarget K n).app j ≫ (objectCocone K).ι.app j := rfl

/-- The source endpoint commutes with each original total-edge injection. -/
theorem source_compat (n : SimplexCategoryᵒᵖ) (j : J) :
    (edgeCocone K n).ι.app j ≫ pointSource K n =
      (edgeSource K n).app j ≫ (objectCocone K).ι.app j := rfl

/-- Pairs of original total edges with literally equal middle endpoints. -/
def composableDiagram (n : SimplexCategoryᵒᵖ) : J ⥤ Type u :=
  TypeFunctorPullback.functor (edgeTarget K n) (edgeSource K n)

/-- Pairs of point total edges with equal middle endpoint. -/
abbrev Composable (n : SimplexCategoryᵒᵖ) : Type u :=
  OriginalFilteredPullbackColimit.Fiber (pointTarget K n) (pointSource K n)

/-- The componentwise cocone remembers both original edge images. -/
noncomputable def composableCocone (n : SimplexCategoryᵒᵖ) :
    Cocone (composableDiagram K n) :=
  OriginalFilteredPullbackColimit.cocone (edgeTarget K n) (edgeSource K n)
    (edgeCocone K n) (edgeCocone K n) (objectCocone K)
    (pointTarget K n) (pointSource K n)
    (target_compat K n) (source_compat K n)

variable [IsFiltered J]

/-- Filtered colimits preserve this exact composable-pair pullback. -/
noncomputable def composableIsColimit (n : SimplexCategoryᵒᵖ) :
    IsColimit (composableCocone K n) :=
  OriginalFilteredPullbackColimit.isColimit (edgeTarget K n) (edgeSource K n)
    (edgeCocone K n) (edgeCocone K n) (objectCocone K)
    (SimplicialGraph.TotalSpace.Colimit.degreeIsColimit (graphDiagram K) n)
    (SimplicialGraph.TotalSpace.Colimit.degreeIsColimit (graphDiagram K) n)
    (SimplicialGraph.TotalSpace.Colimit.objectIsColimit (graphDiagram K))
    (pointTarget K n) (pointSource K n)
    (target_compat K n) (source_compat K n)

/-- Each compatible pair has one original stage with the middle vertex equal there. -/
theorem commonStage (n : SimplexCategoryᵒᵖ) (e : Composable K n) :
    ∃ (j : J) (x : (composableDiagram K n).obj j),
      (edgeCocone K n).ι.app j x.1.1 = e.1.1 ∧
      (edgeCocone K n).ι.app j x.1.2 = e.1.2 :=
  OriginalFilteredPullbackColimit.commonStage (edgeTarget K n) (edgeSource K n)
    (edgeCocone K n) (edgeCocone K n) (objectCocone K)
    (SimplicialGraph.TotalSpace.Colimit.degreeIsColimit (graphDiagram K) n)
    (SimplicialGraph.TotalSpace.Colimit.degreeIsColimit (graphDiagram K) n)
    (SimplicialGraph.TotalSpace.Colimit.objectIsColimit (graphDiagram K))
    (pointTarget K n) (pointSource K n)
    (target_compat K n) (source_compat K n) e

end DaggerModels.OriginalOrdinaryComposableEdges
