import OriginalOrdinaryComposableEdges
import DaggerModels.SimplicialEnrichment

/-!
# Original identity and composition on ordinary total edges

These are the original simplicial-category operations, with both endpoint
labels retained.  No filtered colimit is used in this file.
-/

open CategoryTheory MonoidalCategory

universe u

namespace DaggerModels.OriginalOrdinaryTotalEdgeOperations.Stage

variable {J : Type u} [SmallCategory J]
variable (K : J ⥤ SimplicialCat.{u, u})

open OriginalOrdinaryComposableEdges

/-- The original enriched identity, including both endpoint labels. -/
def identity (j : J) (n : SimplexCategoryᵒᵖ) (x : (K.obj j).Obj) :
    (SimplicialGraph.TotalSpace.edges ((graphDiagram K).obj j)).obj n :=
  ⟨x, x, (eId SSet x).app n PUnit.unit⟩

@[simp] theorem identity_source (j : J) (n : SimplexCategoryᵒᵖ)
    (x : (K.obj j).Obj) : (identity K j n x).1 = x := rfl

@[simp] theorem identity_target (j : J) (n : SimplexCategoryᵒᵖ)
    (x : (K.obj j).Obj) : (identity K j n x).2.1 = x := rfl

/-- Enriched functors preserve the total-edge identity. -/
theorem identity_functor {i j : J} (α : i ⟶ j) (n : SimplexCategoryᵒᵖ)
    (x : (K.obj i).Obj) :
    (SimplicialGraph.TotalSpace.edgeMap ((graphDiagram K).map α)).app n
      (identity K i n x) = identity K j n ((K.map α).obj x) := by
  have h := congrArg (fun f ↦ f.app n PUnit.unit) ((K.map α).map_id x)
  exact congrArg (fun e ↦ (⟨(K.map α).obj x, (K.map α).obj x, e⟩ :
    (SimplicialGraph.TotalSpace.edges ((graphDiagram K).obj j)).obj n)) h

/-- The identity commutes with every ordinary simplex operator. -/
theorem identity_simplex (j : J) {n m : SimplexCategoryᵒᵖ} (β : n ⟶ m)
    (x : (K.obj j).Obj) :
    (SimplicialGraph.TotalSpace.edges ((graphDiagram K).obj j)).map β
      (identity K j n x) = identity K j m x := by
  have h := (congrFun ((eId SSet x).naturality β) PUnit.unit).symm
  exact congrArg (fun e ↦ (⟨x, x, e⟩ :
    (SimplicialGraph.TotalSpace.edges ((graphDiagram K).obj j)).obj m)) h

/-- The original enriched composite, with its outer endpoint labels. -/
def composition (j : J) (n : SimplexCategoryᵒᵖ) :
    (composableDiagram K n).obj j → (edgeDegreeDiagram K n).obj j
  | ⟨(⟨x, y, f⟩, ⟨y', z, g⟩), h⟩ => by
      change y = y' at h
      subst y'
      exact ⟨x, z, (eComp SSet (show (K.obj j).Obj from x) y z).app n (f, g)⟩

@[simp] theorem composition_source (j : J) (n : SimplexCategoryᵒᵖ)
    (e : (composableDiagram K n).obj j) : (composition K j n e).1 = e.1.1.1 := by
  rcases e with ⟨⟨⟨x, y, f⟩, ⟨y', z, g⟩⟩, h⟩
  change y = y' at h
  subst y'
  rfl

@[simp] theorem composition_target (j : J) (n : SimplexCategoryᵒᵖ)
    (e : (composableDiagram K n).obj j) : (composition K j n e).2.1 = e.1.2.2.1 := by
  rcases e with ⟨⟨⟨x, y, f⟩, ⟨y', z, g⟩⟩, h⟩
  change y = y' at h
  subst y'
  rfl

/-- Original diagram maps preserve composition on actual compatible pairs. -/
theorem composition_functor {i j : J} (α : i ⟶ j) (n : SimplexCategoryᵒᵖ)
    (e : (composableDiagram K n).obj i) :
    (edgeDegreeDiagram K n).map α (composition K i n e) =
      composition K j n ((composableDiagram K n).map α e) := by
  rcases e with ⟨⟨⟨x, y, f⟩, ⟨y', z, g⟩⟩, h⟩
  change y = y' at h
  subst y'
  have hc := congrArg (fun k ↦ k.app n (f, g)) ((K.map α).map_comp x y z)
  exact congrArg (fun t ↦ (⟨(K.map α).obj x, (K.map α).obj z, t⟩ :
    (edgeDegreeDiagram K n).obj j)) hc

/-- A natural transformation from original composable pairs to total edges. -/
def compositionNat (n : SimplexCategoryᵒᵖ) :
    composableDiagram K n ⟶ edgeDegreeDiagram K n where
  app j := composition K j n
  naturality := by
    intro i j α
    funext e
    exact (composition_functor K α n e).symm

/-- Apply a simplex operator to both edges of a compatible pair. -/
def pairSimplex (j : J) {n m : SimplexCategoryᵒᵖ} (β : n ⟶ m) :
    (composableDiagram K n).obj j → (composableDiagram K m).obj j
  | ⟨(e, f), h⟩ =>
    ⟨((SimplicialGraph.TotalSpace.edges ((graphDiagram K).obj j)).map β e,
      (SimplicialGraph.TotalSpace.edges ((graphDiagram K).obj j)).map β f), h⟩

/-- Original composition commutes with every ordinary simplex operator. -/
theorem composition_simplex (j : J) {n m : SimplexCategoryᵒᵖ} (β : n ⟶ m)
    (e : (composableDiagram K n).obj j) :
    (SimplicialGraph.TotalSpace.edges ((graphDiagram K).obj j)).map β
      (composition K j n e) = composition K j m (pairSimplex K j β e) := by
  rcases e with ⟨⟨⟨x, y, f⟩, ⟨y', z, g⟩⟩, h⟩
  change y = y' at h
  subst y'
  have hc := (congrFun ((eComp SSet (show (K.obj j).Obj from x) y z).naturality β)
    (f, g)).symm
  exact congrArg (fun t ↦ (⟨x, z, t⟩ :
    (edgeDegreeDiagram K m).obj j)) hc

end DaggerModels.OriginalOrdinaryTotalEdgeOperations.Stage
