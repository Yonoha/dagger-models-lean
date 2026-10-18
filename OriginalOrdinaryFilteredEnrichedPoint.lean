import OriginalOrdinaryTotalEdgeOperationsNaturality
import OriginalOrdinaryTotalEdgeOperationsLaws

/-!
# The enriched point of an ordinary filtered simplicial-category diagram

The underlying simplicial graph is literally the previously constructed graph
colimit. Its original Hom simplicial sets carry the descended unit and
composition. The enriched laws are recovered from equalities of labelled
total edges; no Hom object is replaced.
-/

open CategoryTheory Limits MonoidalCategory

universe u

namespace DaggerModels.OriginalOrdinaryFilteredEnrichedPoint

open OriginalOrdinaryComposableEdges
open OriginalOrdinaryComposableTriples
open OriginalOrdinaryTotalEdgeOperations
open OriginalOrdinaryTotalEdgeOperations.Naturality
open OriginalOrdinaryTotalEdgeOperations.Laws

variable {J : Type u} [SmallCategory J] [IsFiltered J]
variable (K : J ⥤ SimplicialCat.{u, u})

/-- The accepted ordinary graph colimit, with its exact original Hom fibers. -/
noncomputable abbrev graphPoint : SimplicialGraph.{u} :=
  SimplicialGraph.TotalSpace.Colimit.point (graphDiagram K)

omit [IsFiltered J] in
private theorem hom_of_total_eq (n : SimplexCategoryᵒᵖ)
    (x y : (graphPoint K).Obj)
    {f g : ((graphPoint K).Hom x y).obj n}
    (h : (⟨x, y, f⟩ : (SimplicialGraph.TotalSpace.edges (graphPoint K)).obj n) =
      ⟨x, y, g⟩) : f = g := by
  cases h
  rfl

private theorem left_unit_total (n : SimplexCategoryᵒᵖ)
    (x y : (graphPoint K).Obj) (f : ((graphPoint K).Hom x y).obj n) :
    (⟨x, y, (comp K x x y).app n ((unit K x).app n PUnit.unit, f)⟩ :
      (SimplicialGraph.TotalSpace.edges (graphPoint K)).obj n) =
      ⟨x, y, f⟩ := by
  calc
    (⟨x, y, (comp K x x y).app n ((unit K x).app n PUnit.unit, f)⟩ :
      (SimplicialGraph.TotalSpace.edges (graphPoint K)).obj n) =
        pointComposition K n
          ⟨(⟨x, x, (unit K x).app n PUnit.unit⟩, ⟨x, y, f⟩), rfl⟩ :=
      comp_total K n x x y ((unit K x).app n PUnit.unit) f
    _ = pointComposition K n (pointLeftUnitPair K n ⟨x, y, f⟩) := by
      congr 1
      apply Subtype.ext
      apply Prod.ext
      · exact unit_total K n x
      · rfl
    _ = ⟨x, y, f⟩ := pointLeftUnit K n ⟨x, y, f⟩

private theorem right_unit_total (n : SimplexCategoryᵒᵖ)
    (x y : (graphPoint K).Obj) (f : ((graphPoint K).Hom x y).obj n) :
    (⟨x, y, (comp K x y y).app n (f, (unit K y).app n PUnit.unit)⟩ :
      (SimplicialGraph.TotalSpace.edges (graphPoint K)).obj n) =
      ⟨x, y, f⟩ := by
  calc
    (⟨x, y, (comp K x y y).app n (f, (unit K y).app n PUnit.unit)⟩ :
      (SimplicialGraph.TotalSpace.edges (graphPoint K)).obj n) =
        pointComposition K n
          ⟨(⟨x, y, f⟩, ⟨y, y, (unit K y).app n PUnit.unit⟩), rfl⟩ :=
      comp_total K n x y y f ((unit K y).app n PUnit.unit)
    _ = pointComposition K n (pointRightUnitPair K n ⟨x, y, f⟩) := by
      congr 1
      apply Subtype.ext
      apply Prod.ext
      · rfl
      · exact unit_total K n y
    _ = ⟨x, y, f⟩ := pointRightUnit K n ⟨x, y, f⟩

private theorem assoc_total (n : SimplexCategoryᵒᵖ)
    (w x y z : (graphPoint K).Obj)
    (f : ((graphPoint K).Hom w x).obj n)
    (g : ((graphPoint K).Hom x y).obj n)
    (h : ((graphPoint K).Hom y z).obj n) :
    (⟨w, z, (comp K w y z).app n ((comp K w x y).app n (f, g), h)⟩ :
      (SimplicialGraph.TotalSpace.edges (graphPoint K)).obj n) =
      ⟨w, z, (comp K w x z).app n (f, (comp K x y z).app n (g, h))⟩ := by
  let t : Triple K n :=
    ⟨(⟨(⟨w, x, f⟩, ⟨x, y, g⟩), rfl⟩, ⟨y, z, h⟩), rfl⟩
  have hl : (⟨w, z, (comp K w y z).app n ((comp K w x y).app n (f, g), h)⟩ :
      (SimplicialGraph.TotalSpace.edges (graphPoint K)).obj n) =
      pointComposition K n (pointLeftNestedPair K n t) := by
    rw [comp_total K n w y z ((comp K w x y).app n (f, g)) h]
    congr 1
    apply Subtype.ext
    apply Prod.ext
    · exact comp_total K n w x y f g
    · rfl
  have hr : (⟨w, z, (comp K w x z).app n (f, (comp K x y z).app n (g, h))⟩ :
      (SimplicialGraph.TotalSpace.edges (graphPoint K)).obj n) =
      pointComposition K n (pointRightNestedPair K n t) := by
    rw [comp_total K n w x z f ((comp K x y z).app n (g, h))]
    congr 1
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact comp_total K n x y z g h
  calc
    _ = pointComposition K n (pointLeftNestedPair K n t) := hl
    _ = pointComposition K n (pointRightNestedPair K n t) :=
      pointAssociativity K n t
    _ = _ := hr.symm

/-- The original Hom objects, with the descended simplicial unit and composition. -/
noncomputable def enrichedCategory : EnrichedCategory SSet.{u} (graphPoint K).Obj where
  Hom := (graphPoint K).Hom
  id := unit K
  comp := comp K
  id_comp x y := by
    ext n f
    exact hom_of_total_eq K n x y (left_unit_total K n x y f)
  comp_id x y := by
    ext n f
    exact hom_of_total_eq K n x y (right_unit_total K n x y f)
  assoc w x y z := by
    ext n p
    rcases p with ⟨f, g, h⟩
    exact hom_of_total_eq K n w z (assoc_total K n w x y z f g h)

/-- The enriched colimit candidate retains literally the graph point's objects and Homs. -/
noncomputable def point : SimplicialCat.{u, u} :=
  ⟨(graphPoint K).Obj, enrichedCategory K⟩

/-- Forgetting the enrichment recovers the chosen ordinary graph point. -/
theorem point_graph : SimplicialCat.graphForget.obj (point K) = graphPoint K := rfl

end DaggerModels.OriginalOrdinaryFilteredEnrichedPoint
