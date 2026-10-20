import OriginalOrdinaryTotalEdgeOperations

/-!
# Simplicial naturality of descended ordinary total-edge operations

The two point operations commute with simplex operators.  Exact endpoint
fibers then give the unit and composition maps on original Hom simplicial
sets.  Enriched associativity and unit laws are separate obligations.
-/

open CategoryTheory Limits MonoidalCategory

universe u

namespace DaggerModels.OriginalOrdinaryTotalEdgeOperations.Naturality

open OriginalOrdinaryComposableEdges
open OriginalOrdinaryTotalEdgeOperations.Stage
open OriginalOrdinaryTotalEdgeOperations

variable {J : Type u} [SmallCategory J]
variable (K : J ⥤ SimplicialCat.{u, u})

/-- An ordinary simplex operator on total edges of the graph point. -/
noncomputable def edgeSimplex {n m : SimplexCategoryᵒᵖ} (β : n ⟶ m) :
    (edgeCocone K n).pt ⟶ (edgeCocone K m).pt :=
  (SimplicialGraph.TotalSpace.edges
    (SimplicialGraph.TotalSpace.Colimit.point (graphDiagram K))).map β

/-- The operator commutes with each original total-edge leg. -/
theorem edgeSimplex_leg {n m : SimplexCategoryᵒᵖ} (β : n ⟶ m)
    (j : J) (e : (edgeDegreeDiagram K n).obj j) :
    edgeSimplex K β ((edgeCocone K n).ι.app j e) =
      (edgeCocone K m).ι.app j
        ((SimplicialGraph.TotalSpace.edges ((graphDiagram K).obj j)).map β e) := by
  exact (congrFun ((SimplicialGraph.TotalSpace.edgeMap
    (SimplicialGraph.TotalSpace.Colimit.leg (graphDiagram K) j)).naturality β) e).symm

/-- The descended identity is compatible with ordinary simplex operators. -/
theorem pointIdentity_simplex {n m : SimplexCategoryᵒᵖ} (β : n ⟶ m)
    (x : (objectCocone K).pt) :
    edgeSimplex K β (pointIdentity K n x) = pointIdentity K m x := by
  have h : pointIdentity K n ≫ edgeSimplex K β = pointIdentity K m := by
    apply (SimplicialGraph.TotalSpace.Colimit.objectIsColimit (graphDiagram K)).hom_ext
    intro j
    funext y
    change edgeSimplex K β
        (pointIdentity K n ((objectCocone K).ι.app j y)) =
      pointIdentity K m ((objectCocone K).ι.app j y)
    rw [pointIdentity_leg, pointIdentity_leg, edgeSimplex_leg,
      identity_simplex]
  exact congrFun h x

/-- Apply a simplex operator to both point total edges in a compatible pair. -/
noncomputable def pairSimplex {n m : SimplexCategoryᵒᵖ} (β : n ⟶ m) :
    (composableCocone K n).pt ⟶ (composableCocone K m).pt
  | ⟨(e, f), h⟩ => ⟨(edgeSimplex K β e, edgeSimplex K β f), h⟩

/-- The pair operator commutes with every original compatible-pair leg. -/
theorem pairSimplex_leg {n m : SimplexCategoryᵒᵖ} (β : n ⟶ m)
    (j : J) (e : (composableDiagram K n).obj j) :
    pairSimplex K β ((composableCocone K n).ι.app j e) =
      (composableCocone K m).ι.app j (Stage.pairSimplex K j β e) := by
  apply Subtype.ext
  apply Prod.ext
  · exact edgeSimplex_leg K β j e.1.1
  · exact edgeSimplex_leg K β j e.1.2

variable [IsFiltered J]

/-- Descended composition commutes with ordinary simplex operators. -/
theorem pointComposition_simplex {n m : SimplexCategoryᵒᵖ} (β : n ⟶ m)
    (e : (composableCocone K n).pt) :
    edgeSimplex K β (pointComposition K n e) =
      pointComposition K m (pairSimplex K β e) := by
  have h : pointComposition K n ≫ edgeSimplex K β =
      pairSimplex K β ≫ pointComposition K m := by
    apply (composableIsColimit K n).hom_ext
    intro j
    funext x
    change edgeSimplex K β
        (pointComposition K n ((composableCocone K n).ι.app j x)) =
      pointComposition K m
        (pairSimplex K β ((composableCocone K n).ι.app j x))
    rw [pointComposition_leg, pairSimplex_leg, pointComposition_leg,
      edgeSimplex_leg, Stage.composition_simplex]
  exact congrFun h e

private noncomputable def unitFiber (n : SimplexCategoryᵒᵖ)
    (x : (SimplicialGraph.TotalSpace.Colimit.point (graphDiagram K)).Obj) :
    {e : (SimplicialGraph.TotalSpace.edges
      (SimplicialGraph.TotalSpace.Colimit.point (graphDiagram K))).obj n //
      e.1 = x ∧ e.2.1 = x} :=
  ⟨pointIdentity K n x, by
    constructor
    · exact congrFun (pointIdentity_source K n) x
    · exact congrFun (pointIdentity_target K n) x⟩

/-- The actual simplicial unit map into an exact Hom fiber. -/
noncomputable def unit (x : (SimplicialGraph.TotalSpace.Colimit.point
    (graphDiagram K)).Obj) :
    𝟙_ SSet.{u} ⟶ (SimplicialGraph.TotalSpace.Colimit.point (graphDiagram K)).Hom x x where
  app n _ := SimplicialGraph.TotalSpace.fiberEquiv
    (SimplicialGraph.TotalSpace.Colimit.point (graphDiagram K)) x x n
      (unitFiber K n x)
  naturality {n m} β := by
    funext e
    change SimplicialGraph.TotalSpace.fiberEquiv
      (SimplicialGraph.TotalSpace.Colimit.point (graphDiagram K)) x x m
        (unitFiber K m x) =
      ((SimplicialGraph.TotalSpace.Colimit.point (graphDiagram K)).Hom x x).map β
        (SimplicialGraph.TotalSpace.fiberEquiv
          (SimplicialGraph.TotalSpace.Colimit.point (graphDiagram K)) x x n
          (unitFiber K n x))
    rw [← SimplicialGraph.TotalSpace.fiberEquiv_naturality
      (SimplicialGraph.TotalSpace.Colimit.point (graphDiagram K)) x x β
      (unitFiber K n x)]
    congr 1
    apply Subtype.ext
    exact (pointIdentity_simplex K β x).symm

/-- A pair of typed Hom simplices as a literal compatible pair of total edges. -/
private def homPair (n : SimplexCategoryᵒᵖ)
    (x y z : (SimplicialGraph.TotalSpace.Colimit.point (graphDiagram K)).Obj)
    (p : ((SimplicialGraph.TotalSpace.Colimit.point (graphDiagram K)).Hom x y ⊗
      (SimplicialGraph.TotalSpace.Colimit.point (graphDiagram K)).Hom y z).obj n) :
    (composableCocone K n).pt :=
  ⟨(⟨x, y, p.1⟩, ⟨y, z, p.2⟩), rfl⟩

private noncomputable def compFiber (n : SimplexCategoryᵒᵖ)
    (x y z : (SimplicialGraph.TotalSpace.Colimit.point (graphDiagram K)).Obj)
    (p : ((SimplicialGraph.TotalSpace.Colimit.point (graphDiagram K)).Hom x y ⊗
      (SimplicialGraph.TotalSpace.Colimit.point (graphDiagram K)).Hom y z).obj n) :
    {e : (SimplicialGraph.TotalSpace.edges
      (SimplicialGraph.TotalSpace.Colimit.point (graphDiagram K))).obj n //
      e.1 = x ∧ e.2.1 = z} :=
  ⟨pointComposition K n (homPair K n x y z p), by
    constructor
    · exact pointComposition_source K n (homPair K n x y z p)
    · exact pointComposition_target K n (homPair K n x y z p)⟩

/-- The actual simplicial composition map into an exact Hom fiber. -/
noncomputable def comp
    (x y z : (SimplicialGraph.TotalSpace.Colimit.point (graphDiagram K)).Obj) :
    (SimplicialGraph.TotalSpace.Colimit.point (graphDiagram K)).Hom x y ⊗
      (SimplicialGraph.TotalSpace.Colimit.point (graphDiagram K)).Hom y z ⟶
      (SimplicialGraph.TotalSpace.Colimit.point (graphDiagram K)).Hom x z where
  app n p := SimplicialGraph.TotalSpace.fiberEquiv
    (SimplicialGraph.TotalSpace.Colimit.point (graphDiagram K)) x z n
      (compFiber K n x y z p)
  naturality {n m} β := by
    funext p
    change SimplicialGraph.TotalSpace.fiberEquiv
      (SimplicialGraph.TotalSpace.Colimit.point (graphDiagram K)) x z m
        (compFiber K m x y z
          (((SimplicialGraph.TotalSpace.Colimit.point (graphDiagram K)).Hom x y ⊗
            (SimplicialGraph.TotalSpace.Colimit.point (graphDiagram K)).Hom y z).map β p)) =
      ((SimplicialGraph.TotalSpace.Colimit.point (graphDiagram K)).Hom x z).map β
        (SimplicialGraph.TotalSpace.fiberEquiv
          (SimplicialGraph.TotalSpace.Colimit.point (graphDiagram K)) x z n
          (compFiber K n x y z p))
    rw [← SimplicialGraph.TotalSpace.fiberEquiv_naturality
      (SimplicialGraph.TotalSpace.Colimit.point (graphDiagram K)) x z β
      (compFiber K n x y z p)]
    congr 1
    apply Subtype.ext
    change pointComposition K m
        (homPair K m x y z
          (((SimplicialGraph.TotalSpace.Colimit.point (graphDiagram K)).Hom x y ⊗
            (SimplicialGraph.TotalSpace.Colimit.point (graphDiagram K)).Hom y z).map β p)) =
      (SimplicialGraph.TotalSpace.edges
        (SimplicialGraph.TotalSpace.Colimit.point (graphDiagram K))).map β
        (pointComposition K n (homPair K n x y z p))
    have hp : homPair K m x y z
        (((SimplicialGraph.TotalSpace.Colimit.point (graphDiagram K)).Hom x y ⊗
          (SimplicialGraph.TotalSpace.Colimit.point (graphDiagram K)).Hom y z).map β p) =
        pairSimplex K β (homPair K n x y z p) := rfl
    rw [hp]
    exact (pointComposition_simplex K β (homPair K n x y z p)).symm

omit [IsFiltered J] in
/-- Reinsert both endpoint labels around the simplicial unit. -/
theorem unit_total (n : SimplexCategoryᵒᵖ)
    (x : (SimplicialGraph.TotalSpace.Colimit.point (graphDiagram K)).Obj) :
    (⟨x, x, (unit K x).app n PUnit.unit⟩ :
      (SimplicialGraph.TotalSpace.edges
        (SimplicialGraph.TotalSpace.Colimit.point (graphDiagram K))).obj n) =
      pointIdentity K n x := by
  have h := (SimplicialGraph.TotalSpace.fiberEquiv
    (SimplicialGraph.TotalSpace.Colimit.point (graphDiagram K)) x x n).left_inv
      (unitFiber K n x)
  exact congrArg Subtype.val h

/-- Reinsert the outer endpoint labels around simplicial composition. -/
theorem comp_total (n : SimplexCategoryᵒᵖ)
    (x y z : (SimplicialGraph.TotalSpace.Colimit.point (graphDiagram K)).Obj)
    (f : ((SimplicialGraph.TotalSpace.Colimit.point (graphDiagram K)).Hom x y).obj n)
    (g : ((SimplicialGraph.TotalSpace.Colimit.point (graphDiagram K)).Hom y z).obj n) :
    (⟨x, z, (comp K x y z).app n (f, g)⟩ :
      (SimplicialGraph.TotalSpace.edges
        (SimplicialGraph.TotalSpace.Colimit.point (graphDiagram K))).obj n) =
      pointComposition K n ⟨(⟨x, y, f⟩, ⟨y, z, g⟩), rfl⟩ := by
  have h := (SimplicialGraph.TotalSpace.fiberEquiv
    (SimplicialGraph.TotalSpace.Colimit.point (graphDiagram K)) x z n).left_inv
      (compFiber K n x y z (f, g))
  exact congrArg Subtype.val h

end DaggerModels.OriginalOrdinaryTotalEdgeOperations.Naturality
