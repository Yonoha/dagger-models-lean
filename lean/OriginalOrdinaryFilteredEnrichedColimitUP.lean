import OriginalOrdinaryFilteredEnrichedPointLegs
import DaggerModels.SimplicialColimits

/-!
# Universal property of the original filtered enriched point

The graph colimit supplies the underlying map to an arbitrary enriched
cocone.  The object and compatible-pair Type colimit universal properties
show that this map respects the descended unit and composition.  The
comparison with the semantic colimit is stated after this direct proof.
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

/-- The accepted graph colimit gives the underlying map to any enriched cocone. -/
noncomputable def graphDesc (s : Cocone K) :
    graphPoint K ⟶ SimplicialCat.graphForget.obj s.pt :=
  SimplicialGraph.TotalSpace.Colimit.desc (graphDiagram K)
    (SimplicialCat.graphForget.mapCocone s)

omit [IsFiltered J] in
private theorem graphDesc_object_leg (s : Cocone K) (j : J) (x : (K.obj j).Obj) :
    (graphDesc K s).obj ((objectCocone K).ι.app j x) =
      (s.ι.app j).obj x :=
  SimplicialGraph.TotalSpace.Colimit.objectDesc_ι (graphDiagram K)
    (SimplicialCat.graphForget.mapCocone s) j x

omit [IsFiltered J] in
private theorem graphDesc_edge_leg (s : Cocone K) (j : J) :
    SimplicialGraph.TotalSpace.edgeMap
        (SimplicialGraph.TotalSpace.Colimit.leg (graphDiagram K) j) ≫
      SimplicialGraph.TotalSpace.edgeMap (graphDesc K s) =
    SimplicialGraph.TotalSpace.edgeMap
      (SimplicialCat.graphForget.map (s.ι.app j)) := by
  change SimplicialGraph.TotalSpace.edgeFunctor.map
      (SimplicialGraph.TotalSpace.Colimit.leg (graphDiagram K) j) ≫
      SimplicialGraph.TotalSpace.edgeFunctor.map (graphDesc K s) =
    SimplicialGraph.TotalSpace.edgeFunctor.map
      (SimplicialCat.graphForget.map (s.ι.app j))
  rw [← SimplicialGraph.TotalSpace.edgeFunctor.map_comp]
  exact congrArg SimplicialGraph.TotalSpace.edgeFunctor.map
    (SimplicialGraph.TotalSpace.Colimit.leg_desc (graphDiagram K)
      (SimplicialCat.graphForget.mapCocone s) j)

omit [IsFiltered J] in
private theorem graphDesc_identity (s : Cocone K) (n : SimplexCategoryᵒᵖ)
    (x : (graphPoint K).Obj) :
    (SimplicialGraph.TotalSpace.edgeMap (graphDesc K s)).app n
        (pointIdentity K n x) =
      ⟨(graphDesc K s).obj x, (graphDesc K s).obj x,
        (eId SSet (show s.pt.Obj from (graphDesc K s).obj x)).app n PUnit.unit⟩ := by
  obtain ⟨j, y, hy⟩ := Types.jointly_surjective_of_isColimit
    (SimplicialGraph.TotalSpace.Colimit.objectIsColimit (graphDiagram K)) x
  rw [← hy]
  change (SimplicialGraph.TotalSpace.edgeMap (graphDesc K s)).app n
      (pointIdentity K n ((objectCocone K).ι.app j y)) =
    ⟨(graphDesc K s).obj ((objectCocone K).ι.app j y),
      (graphDesc K s).obj ((objectCocone K).ι.app j y),
      (eId SSet (show s.pt.Obj from
        (graphDesc K s).obj ((objectCocone K).ι.app j y))).app n PUnit.unit⟩
  rw [pointIdentity_leg K n j y]
  have he := congrFun (NatTrans.congr_app (graphDesc_edge_leg K s j) n)
    (identity K j n y)
  have hu := congrArg (fun f ↦ f.app n PUnit.unit) ((s.ι.app j).map_id y)
  change (SimplicialGraph.TotalSpace.edgeMap (graphDesc K s)).app n
      ((SimplicialGraph.TotalSpace.edgeMap
        (SimplicialGraph.TotalSpace.Colimit.leg (graphDiagram K) j)).app n
          (identity K j n y)) = _
  rw [graphDesc_object_leg K s j y]
  calc
    _ = (SimplicialGraph.TotalSpace.edgeMap
          (SimplicialCat.graphForget.map (s.ι.app j))).app n
            (identity K j n y) := he
    _ = _ := by
      change (⟨(s.ι.app j).obj y, (s.ι.app j).obj y,
          ((s.ι.app j).map y y).app n
            ((eId SSet (show (K.obj j).Obj from y)).app n PUnit.unit)⟩ :
          (SimplicialGraph.TotalSpace.edges
            (SimplicialCat.graphForget.obj s.pt)).obj n) = _
      exact congrArg (fun e ↦ (⟨(s.ι.app j).obj y,
        (s.ι.app j).obj y, e⟩ :
        (SimplicialGraph.TotalSpace.edges
          (SimplicialCat.graphForget.obj s.pt)).obj n)) hu

private def targetComposable (C : SimplicialCat.{u, u})
    (n : SimplexCategoryᵒᵖ) : Type u :=
  { e : (SimplicialGraph.TotalSpace.edges
      (SimplicialCat.graphForget.obj C)).obj n ×
      (SimplicialGraph.TotalSpace.edges
        (SimplicialCat.graphForget.obj C)).obj n // e.1.2.1 = e.2.1 }

private def targetComposition (C : SimplicialCat.{u, u})
    (n : SimplexCategoryᵒᵖ) : targetComposable C n →
      (SimplicialGraph.TotalSpace.edges
        (SimplicialCat.graphForget.obj C)).obj n
  | ⟨(⟨x, y, f⟩, ⟨y', z, g⟩), h⟩ => by
      change y = y' at h
      subst y'
      exact ⟨x, z, (eComp SSet (show C.Obj from x) y z).app n (f, g)⟩

private noncomputable def pairDesc (s : Cocone K) (n : SimplexCategoryᵒᵖ) :
    (composableCocone K n).pt → targetComposable s.pt n
  | ⟨(a, b), h⟩ =>
      ⟨((SimplicialGraph.TotalSpace.edgeMap (graphDesc K s)).app n a,
        (SimplicialGraph.TotalSpace.edgeMap (graphDesc K s)).app n b),
        congrArg (graphDesc K s).obj h⟩

private theorem graphDesc_composition (s : Cocone K) (n : SimplexCategoryᵒᵖ)
    (e : (composableCocone K n).pt) :
    (SimplicialGraph.TotalSpace.edgeMap (graphDesc K s)).app n
        (pointComposition K n e) =
      targetComposition s.pt n (pairDesc K s n e) := by
  have h : pointComposition K n ≫
        (SimplicialGraph.TotalSpace.edgeMap (graphDesc K s)).app n =
      pairDesc K s n ≫ targetComposition s.pt n := by
    apply (composableIsColimit K n).hom_ext
    intro j
    funext q
    rcases q with ⟨⟨⟨x, y, f⟩, ⟨y', z, g⟩⟩, hq⟩
    change y = y' at hq
    subst y'
    change (SimplicialGraph.TotalSpace.edgeMap (graphDesc K s)).app n
        (pointComposition K n
          ((composableCocone K n).ι.app j
            (⟨(⟨x, y, f⟩, ⟨y, z, g⟩), rfl⟩ :
              (composableDiagram K n).obj j))) =
      targetComposition s.pt n
        (pairDesc K s n
          ((composableCocone K n).ι.app j
            (⟨(⟨x, y, f⟩, ⟨y, z, g⟩), rfl⟩ :
              (composableDiagram K n).obj j)))
    rw [pointComposition_leg K n j]
    have hl := congrFun (NatTrans.congr_app (graphDesc_edge_leg K s j) n)
      (⟨x, y, f⟩ :
        (SimplicialGraph.TotalSpace.edges ((graphDiagram K).obj j)).obj n)
    have hr := congrFun (NatTrans.congr_app (graphDesc_edge_leg K s j) n)
      (⟨y, z, g⟩ :
        (SimplicialGraph.TotalSpace.edges ((graphDiagram K).obj j)).obj n)
    have hc := congrFun (NatTrans.congr_app (graphDesc_edge_leg K s j) n)
      (composition K j n
        (⟨(⟨x, y, f⟩, ⟨y, z, g⟩), rfl⟩ :
          (composableDiagram K n).obj j))
    change (SimplicialGraph.TotalSpace.edgeMap (graphDesc K s)).app n
        ((SimplicialGraph.TotalSpace.edgeMap
          (SimplicialGraph.TotalSpace.Colimit.leg (graphDiagram K) j)).app n
            (⟨x, y, f⟩ :
              (SimplicialGraph.TotalSpace.edges ((graphDiagram K).obj j)).obj n)) =
      (SimplicialGraph.TotalSpace.edgeMap
        (SimplicialCat.graphForget.map (s.ι.app j))).app n ⟨x, y, f⟩ at hl
    change (SimplicialGraph.TotalSpace.edgeMap (graphDesc K s)).app n
        ((SimplicialGraph.TotalSpace.edgeMap
          (SimplicialGraph.TotalSpace.Colimit.leg (graphDiagram K) j)).app n
            (⟨y, z, g⟩ :
              (SimplicialGraph.TotalSpace.edges ((graphDiagram K).obj j)).obj n)) =
      (SimplicialGraph.TotalSpace.edgeMap
        (SimplicialCat.graphForget.map (s.ι.app j))).app n ⟨y, z, g⟩ at hr
    change (SimplicialGraph.TotalSpace.edgeMap (graphDesc K s)).app n
        ((SimplicialGraph.TotalSpace.edgeMap
          (SimplicialGraph.TotalSpace.Colimit.leg (graphDiagram K) j)).app n
            (composition K j n
              (⟨(⟨x, y, f⟩, ⟨y, z, g⟩), rfl⟩ :
                (composableDiagram K n).obj j))) =
      (SimplicialGraph.TotalSpace.edgeMap
        (SimplicialCat.graphForget.map (s.ι.app j))).app n
          (composition K j n
            (⟨(⟨x, y, f⟩, ⟨y, z, g⟩), rfl⟩ :
              (composableDiagram K n).obj j)) at hc
    have hm := congrArg (fun p ↦ p.app n (f, g)) ((s.ι.app j).map_comp x y z)
    change (SimplicialGraph.TotalSpace.edgeMap (graphDesc K s)).app n
        ((SimplicialGraph.TotalSpace.edgeMap
          (SimplicialGraph.TotalSpace.Colimit.leg (graphDiagram K) j)).app n
            (composition K j n
              (⟨(⟨x, y, f⟩, ⟨y, z, g⟩), rfl⟩ :
                (composableDiagram K n).obj j))) = _
    rw [hc]
    change (⟨(s.ι.app j).obj x, (s.ι.app j).obj z,
        ((s.ι.app j).map x z).app n
          ((eComp SSet (show (K.obj j).Obj from x) y z).app n (f, g))⟩ :
        (SimplicialGraph.TotalSpace.edges
          (SimplicialCat.graphForget.obj s.pt)).obj n) =
      targetComposition s.pt n
        (⟨((SimplicialGraph.TotalSpace.edgeMap (graphDesc K s)).app n
              ((SimplicialGraph.TotalSpace.edgeMap
                (SimplicialGraph.TotalSpace.Colimit.leg (graphDiagram K) j)).app n
                  (⟨x, y, f⟩ :
                    (SimplicialGraph.TotalSpace.edges ((graphDiagram K).obj j)).obj n)),
            (SimplicialGraph.TotalSpace.edgeMap (graphDesc K s)).app n
              ((SimplicialGraph.TotalSpace.edgeMap
                (SimplicialGraph.TotalSpace.Colimit.leg (graphDiagram K) j)).app n
                  (⟨y, z, g⟩ :
                    (SimplicialGraph.TotalSpace.edges ((graphDiagram K).obj j)).obj n))),
          rfl⟩ : targetComposable s.pt n)
    have hp :
        (⟨((SimplicialGraph.TotalSpace.edgeMap (graphDesc K s)).app n
              ((SimplicialGraph.TotalSpace.edgeMap
                (SimplicialGraph.TotalSpace.Colimit.leg (graphDiagram K) j)).app n
                  (⟨x, y, f⟩ :
                    (SimplicialGraph.TotalSpace.edges ((graphDiagram K).obj j)).obj n)),
            (SimplicialGraph.TotalSpace.edgeMap (graphDesc K s)).app n
              ((SimplicialGraph.TotalSpace.edgeMap
                (SimplicialGraph.TotalSpace.Colimit.leg (graphDiagram K) j)).app n
                  (⟨y, z, g⟩ :
                    (SimplicialGraph.TotalSpace.edges ((graphDiagram K).obj j)).obj n))),
          rfl⟩ : targetComposable s.pt n) =
        ⟨((SimplicialGraph.TotalSpace.edgeMap
              (SimplicialCat.graphForget.map (s.ι.app j))).app n ⟨x, y, f⟩,
            (SimplicialGraph.TotalSpace.edgeMap
              (SimplicialCat.graphForget.map (s.ι.app j))).app n ⟨y, z, g⟩),
          rfl⟩ := by
      apply Subtype.ext
      exact Prod.ext hl hr
    rw [hp]
    change (⟨(s.ι.app j).obj x, (s.ι.app j).obj z,
        ((s.ι.app j).map x z).app n
          ((eComp SSet (show (K.obj j).Obj from x) y z).app n (f, g))⟩ :
        (SimplicialGraph.TotalSpace.edges
          (SimplicialCat.graphForget.obj s.pt)).obj n) =
      ⟨(s.ι.app j).obj x, (s.ι.app j).obj z,
        (eComp SSet (show s.pt.Obj from (s.ι.app j).obj x)
          ((s.ι.app j).obj y) ((s.ι.app j).obj z)).app n
          (((s.ι.app j).map x y).app n f,
            ((s.ι.app j).map y z).app n g)⟩
    exact congrArg (fun t ↦ (⟨(s.ι.app j).obj x,
      (s.ι.app j).obj z, t⟩ :
        (SimplicialGraph.TotalSpace.edges
          (SimplicialCat.graphForget.obj s.pt)).obj n)) hm
  exact congrFun h e

/-- The graph descent of an arbitrary enriched cocone is itself enriched. -/
noncomputable def desc (s : Cocone K) : point K ⟶ s.pt where
  obj := (graphDesc K s).obj
  map := (graphDesc K s).map
  map_id x := by
    ext n e
    cases e
    have h := graphDesc_identity K s n x
    rw [← unit_total K n x] at h
    change (⟨(graphDesc K s).obj x, (graphDesc K s).obj x,
        ((graphDesc K s).map x x).app n ((unit K x).app n PUnit.unit)⟩ :
        (SimplicialGraph.TotalSpace.edges
          (SimplicialCat.graphForget.obj s.pt)).obj n) =
      ⟨(graphDesc K s).obj x, (graphDesc K s).obj x,
        (eId SSet (show s.pt.Obj from (graphDesc K s).obj x)).app n PUnit.unit⟩ at h
    change ((graphDesc K s).map x x).app n ((unit K x).app n PUnit.unit) =
      (eId SSet (show s.pt.Obj from (graphDesc K s).obj x)).app n PUnit.unit
    simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using h
  map_comp x y z := by
    ext n p
    rcases p with ⟨f, g⟩
    have h := graphDesc_composition K s n
      (⟨(⟨x, y, f⟩, ⟨y, z, g⟩), rfl⟩ : (composableCocone K n).pt)
    rw [← comp_total K n x y z f g] at h
    change (⟨(graphDesc K s).obj x, (graphDesc K s).obj z,
        ((graphDesc K s).map x z).app n ((comp K x y z).app n (f, g))⟩ :
        (SimplicialGraph.TotalSpace.edges
          (SimplicialCat.graphForget.obj s.pt)).obj n) =
      ⟨(graphDesc K s).obj x, (graphDesc K s).obj z,
        (eComp SSet (show s.pt.Obj from (graphDesc K s).obj x)
          ((graphDesc K s).obj y) ((graphDesc K s).obj z)).app n
          (((graphDesc K s).map x y).app n f,
            ((graphDesc K s).map y z).app n g)⟩ at h
    change ((graphDesc K s).map x z).app n ((comp K x y z).app n (f, g)) =
      (eComp SSet (show s.pt.Obj from (graphDesc K s).obj x)
        ((graphDesc K s).obj y) ((graphDesc K s).obj z)).app n
          (((graphDesc K s).map x y).app n f,
            ((graphDesc K s).map y z).app n g)
    simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using h

/-- Descent has exactly the accepted underlying graph map. -/
theorem desc_graph (s : Cocone K) :
    SimplicialCat.graphForget.map (desc K s) = graphDesc K s := rfl

/-- The descended enriched map has every original enriched leg. -/
theorem leg_desc (s : Cocone K) (j : J) :
    leg K j ≫ desc K s = s.ι.app j := by
  apply (SimplicialCat.graphForget).map_injective
  change SimplicialGraph.TotalSpace.Colimit.leg (graphDiagram K) j ≫
      graphDesc K s = (SimplicialCat.graphForget.mapCocone s).ι.app j
  exact SimplicialGraph.TotalSpace.Colimit.leg_desc (graphDiagram K)
    (SimplicialCat.graphForget.mapCocone s) j

/-- The original filtered enriched cocone is an actual ordinary colimit. -/
noncomputable def isColimit : IsColimit (cocone K) where
  desc := desc K
  fac := leg_desc K
  uniq s m hm := by
    apply (SimplicialCat.graphForget).map_injective
    have hu := (SimplicialGraph.TotalSpace.Colimit.isColimit
      (graphDiagram K)).uniq (SimplicialCat.graphForget.mapCocone s)
      (SimplicialCat.graphForget.map m) (fun j ↦ by
        simpa only [← Functor.map_comp, leg_graph] using
          congrArg SimplicialCat.graphForget.map (hm j))
    exact hu

end DaggerModels.OriginalOrdinaryFilteredEnrichedPoint
