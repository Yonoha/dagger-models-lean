import OriginalOrdinaryFilteredEnrichedPoint

/-!
# Original enriched legs into the filtered enriched point

Each enriched leg uses exactly the object and Hom maps of the accepted
ordinary graph leg. The enriched functor laws follow from its original total
edge equations and the public total-edge recovery of unit and composition.
-/

open CategoryTheory Limits MonoidalCategory

universe u

namespace DaggerModels.OriginalOrdinaryFilteredEnrichedPoint

open OriginalOrdinaryComposableEdges
open OriginalOrdinaryTotalEdgeOperations
open OriginalOrdinaryTotalEdgeOperations.Stage
open OriginalOrdinaryTotalEdgeOperations.Naturality

variable {J : Type u} [SmallCategory J] [IsFiltered J]
variable (K : J ⥤ SimplicialCat.{u, u})

/-- An original enriched leg, with exactly the accepted graph leg's maps. -/
noncomputable def leg (j : J) : K.obj j ⟶ point K where
  obj := (SimplicialGraph.TotalSpace.Colimit.leg (graphDiagram K) j).obj
  map := (SimplicialGraph.TotalSpace.Colimit.leg (graphDiagram K) j).map
  map_id x := by
    ext n e
    cases e
    let a := (SimplicialGraph.TotalSpace.Colimit.leg (graphDiagram K) j).obj x
    have h : (⟨a, a,
        ((SimplicialGraph.TotalSpace.Colimit.leg (graphDiagram K) j).map x x).app n
          ((eId SSet x).app n PUnit.unit)⟩ :
          (SimplicialGraph.TotalSpace.edges (graphPoint K)).obj n) =
        ⟨a, a, (unit K a).app n PUnit.unit⟩ := by
      calc
        _ = (edgeCocone K n).ι.app j (identity K j n x) := rfl
        _ = pointIdentity K n a := (pointIdentity_leg K n j x).symm
        _ = _ := (unit_total K n a).symm
    simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using h
  map_comp x y z := by
    ext n p
    rcases p with ⟨f, g⟩
    let a := (SimplicialGraph.TotalSpace.Colimit.leg (graphDiagram K) j).obj x
    let b := (SimplicialGraph.TotalSpace.Colimit.leg (graphDiagram K) j).obj y
    let c := (SimplicialGraph.TotalSpace.Colimit.leg (graphDiagram K) j).obj z
    let q : (composableDiagram K n).obj j :=
      ⟨(⟨x, y, f⟩, ⟨y, z, g⟩), rfl⟩
    have h : (⟨a, c,
        ((SimplicialGraph.TotalSpace.Colimit.leg (graphDiagram K) j).map x z).app n
          ((eComp SSet x y z).app n (f, g))⟩ :
          (SimplicialGraph.TotalSpace.edges (graphPoint K)).obj n) =
        ⟨a, c, (comp K a b c).app n
          (((SimplicialGraph.TotalSpace.Colimit.leg (graphDiagram K) j).map x y).app n f,
            ((SimplicialGraph.TotalSpace.Colimit.leg (graphDiagram K) j).map y z).app n g)⟩ := by
      calc
        _ = (edgeCocone K n).ι.app j (composition K j n q) := rfl
        _ = pointComposition K n ((composableCocone K n).ι.app j q) :=
          (pointComposition_leg K n j q).symm
        _ = pointComposition K n
            ⟨(⟨a, b,
                ((SimplicialGraph.TotalSpace.Colimit.leg (graphDiagram K) j).map x y).app n f⟩,
              ⟨b, c,
                ((SimplicialGraph.TotalSpace.Colimit.leg (graphDiagram K) j).map y z).app n g⟩),
              rfl⟩ := rfl
        _ = _ := (comp_total K n a b c _ _).symm
    simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using h

/-- Forgetting an enriched leg is literally its original graph leg. -/
theorem leg_graph (j : J) :
    SimplicialCat.graphForget.map (leg K j) =
      SimplicialGraph.TotalSpace.Colimit.leg (graphDiagram K) j := rfl

/-- The original enriched legs form a cocone. -/
noncomputable def cocone : Cocone K where
  pt := point K
  ι := {
    app := leg K
    naturality := by
      intro i j α
      apply (SimplicialCat.graphForget).map_injective
      change (graphDiagram K).map α ≫
          SimplicialGraph.TotalSpace.Colimit.leg (graphDiagram K) j =
        SimplicialGraph.TotalSpace.Colimit.leg (graphDiagram K) i
      exact (SimplicialGraph.TotalSpace.Colimit.cocone (graphDiagram K)).w α }

/-- Forgetting the enriched cocone gives exactly the accepted graph cocone. -/
theorem cocone_graph :
    SimplicialCat.graphForget.mapCocone (cocone K) =
      SimplicialGraph.TotalSpace.Colimit.cocone (graphDiagram K) := rfl

end DaggerModels.OriginalOrdinaryFilteredEnrichedPoint
