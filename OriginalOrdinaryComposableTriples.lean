import OriginalOrdinaryComposableEdges

/-!
# Triples of composable original edges

The second pullback is over the target of the second edge in an original
composable pair and the source of a third original edge.  Its point is the
literal nested fiber product.  Filtered colimits preserve this pullback by
the existing generic Type-valued bridge.
-/

open CategoryTheory Limits

universe u

namespace DaggerModels.OriginalOrdinaryComposableTriples

variable {J : Type u} [SmallCategory J]
variable (K : J ⥤ SimplicialCat.{u, u})

/-- The target of the second original edge in a composable pair. -/
def pairTarget (n : SimplexCategoryᵒᵖ) :
    OriginalOrdinaryComposableEdges.composableDiagram K n ⟶
      SimplicialGraph.TotalSpace.Colimit.objectDiagram
        (OriginalOrdinaryComposableEdges.graphDiagram K) where
  app j e := e.1.2.2.1
  naturality := by
    intro i j α
    funext e
    rfl

/-- The target of the second total edge in a colimit composable pair. -/
noncomputable def pointPairTarget (n : SimplexCategoryᵒᵖ) :
    OriginalOrdinaryComposableEdges.Composable K n ⟶
      (OriginalOrdinaryComposableEdges.objectCocone K).pt :=
  fun e ↦ e.1.2.2.1

/-- The pair-target map retains the original second edge's endpoint. -/
theorem pairTarget_compat (n : SimplexCategoryᵒᵖ) (j : J) :
    (OriginalOrdinaryComposableEdges.composableCocone K n).ι.app j ≫
        pointPairTarget K n =
      (pairTarget K n).app j ≫
        (OriginalOrdinaryComposableEdges.objectCocone K).ι.app j := by
  funext e
  exact congrFun (OriginalOrdinaryComposableEdges.target_compat K n j) e.1.2

/-- Three original total edges, with both middle endpoint equations. -/
def tripleDiagram (n : SimplexCategoryᵒᵖ) : J ⥤ Type u :=
  TypeFunctorPullback.functor (pairTarget K n)
    (OriginalOrdinaryComposableEdges.edgeSource K n)

/-- The literal nested pullback of a colimit composable pair and a third edge. -/
abbrev Triple (n : SimplexCategoryᵒᵖ) : Type u :=
  OriginalFilteredPullbackColimit.Fiber (pointPairTarget K n)
    (OriginalOrdinaryComposableEdges.pointSource K n)

/-- The componentwise cocone retains all three original edge images. -/
noncomputable def tripleCocone (n : SimplexCategoryᵒᵖ) :
    Cocone (tripleDiagram K n) :=
  OriginalFilteredPullbackColimit.cocone (pairTarget K n)
    (OriginalOrdinaryComposableEdges.edgeSource K n)
    (OriginalOrdinaryComposableEdges.composableCocone K n)
    (OriginalOrdinaryComposableEdges.edgeCocone K n)
    (OriginalOrdinaryComposableEdges.objectCocone K)
    (pointPairTarget K n) (OriginalOrdinaryComposableEdges.pointSource K n)
    (pairTarget_compat K n) (OriginalOrdinaryComposableEdges.source_compat K n)

variable [IsFiltered J]

/-- This literal triple cocone is colimiting. -/
noncomputable def tripleIsColimit (n : SimplexCategoryᵒᵖ) :
    IsColimit (tripleCocone K n) :=
  OriginalFilteredPullbackColimit.isColimit (pairTarget K n)
    (OriginalOrdinaryComposableEdges.edgeSource K n)
    (OriginalOrdinaryComposableEdges.composableCocone K n)
    (OriginalOrdinaryComposableEdges.edgeCocone K n)
    (OriginalOrdinaryComposableEdges.objectCocone K)
    (OriginalOrdinaryComposableEdges.composableIsColimit K n)
    (SimplicialGraph.TotalSpace.Colimit.degreeIsColimit
      (OriginalOrdinaryComposableEdges.graphDiagram K) n)
    (SimplicialGraph.TotalSpace.Colimit.objectIsColimit
      (OriginalOrdinaryComposableEdges.graphDiagram K))
    (pointPairTarget K n) (OriginalOrdinaryComposableEdges.pointSource K n)
    (pairTarget_compat K n) (OriginalOrdinaryComposableEdges.source_compat K n)

/-- A compatible colimit triple is represented by three original edges at one stage. -/
theorem commonStage (n : SimplexCategoryᵒᵖ) (e : Triple K n) :
    ∃ (j : J) (x : (tripleDiagram K n).obj j),
      (OriginalOrdinaryComposableEdges.edgeTarget K n).app j x.1.1.1.1 =
        (OriginalOrdinaryComposableEdges.edgeSource K n).app j x.1.1.1.2 ∧
      (OriginalOrdinaryComposableEdges.edgeTarget K n).app j x.1.1.1.2 =
        (OriginalOrdinaryComposableEdges.edgeSource K n).app j x.1.2 ∧
      (OriginalOrdinaryComposableEdges.edgeCocone K n).ι.app j x.1.1.1.1 =
        e.1.1.1.1 ∧
      (OriginalOrdinaryComposableEdges.edgeCocone K n).ι.app j x.1.1.1.2 =
        e.1.1.1.2 ∧
      (OriginalOrdinaryComposableEdges.edgeCocone K n).ι.app j x.1.2 =
        e.1.2 := by
  obtain ⟨j, x, hpair, hthird⟩ := OriginalFilteredPullbackColimit.commonStage
    (pairTarget K n) (OriginalOrdinaryComposableEdges.edgeSource K n)
    (OriginalOrdinaryComposableEdges.composableCocone K n)
    (OriginalOrdinaryComposableEdges.edgeCocone K n)
    (OriginalOrdinaryComposableEdges.objectCocone K)
    (OriginalOrdinaryComposableEdges.composableIsColimit K n)
    (SimplicialGraph.TotalSpace.Colimit.degreeIsColimit
      (OriginalOrdinaryComposableEdges.graphDiagram K) n)
    (SimplicialGraph.TotalSpace.Colimit.objectIsColimit
      (OriginalOrdinaryComposableEdges.graphDiagram K))
    (pointPairTarget K n) (OriginalOrdinaryComposableEdges.pointSource K n)
    (pairTarget_compat K n) (OriginalOrdinaryComposableEdges.source_compat K n) e
  have hfirst := congrArg
    (fun z : OriginalOrdinaryComposableEdges.Composable K n ↦ z.1.1) hpair
  have hsecond := congrArg
    (fun z : OriginalOrdinaryComposableEdges.Composable K n ↦ z.1.2) hpair
  change (OriginalOrdinaryComposableEdges.edgeCocone K n).ι.app j x.1.1.1.1 =
    e.1.1.1.1 at hfirst
  change (OriginalOrdinaryComposableEdges.edgeCocone K n).ι.app j x.1.1.1.2 =
    e.1.1.1.2 at hsecond
  exact ⟨j, x, x.1.1.2, x.2, hfirst, hsecond, hthird⟩

end DaggerModels.OriginalOrdinaryComposableTriples
