import OriginalOrdinaryTotalEdgeOperationsStage

/-!
# Descent of ordinary total-edge identity and composition

The object and compatible-pair colimit universal properties descend the
original enriched operations to the ordinary graph point.  The original leg
equations and outer endpoint equations remain explicit.
-/

open CategoryTheory Limits

universe u

namespace DaggerModels.OriginalOrdinaryTotalEdgeOperations

open OriginalOrdinaryComposableEdges
open OriginalOrdinaryTotalEdgeOperations.Stage

variable {J : Type u} [SmallCategory J]
variable (K : J ⥤ SimplicialCat.{u, u})

/-- Original identities form a cocone from vertices into point total edges. -/
noncomputable def identityCocone (n : SimplexCategoryᵒᵖ) :
    Cocone (SimplicialGraph.TotalSpace.Colimit.objectDiagram (graphDiagram K)) where
  pt := (edgeCocone K n).pt
  ι := {
    app j x := (edgeCocone K n).ι.app j (identity K j n x)
    naturality := by
      intro i j α
      funext x
      change (edgeCocone K n).ι.app j (identity K j n ((K.map α).obj x)) =
        (edgeCocone K n).ι.app i (identity K i n x)
      rw [← identity_functor K α n x]
      exact congrFun ((edgeCocone K n).w α) (identity K i n x) }

/-- The identity edge at any vertex of the graph colimit. -/
noncomputable def pointIdentity (n : SimplexCategoryᵒᵖ) :
    (objectCocone K).pt ⟶ (edgeCocone K n).pt :=
  (SimplicialGraph.TotalSpace.Colimit.objectIsColimit (graphDiagram K)).desc
    (identityCocone K n)

/-- Every original identity maps to the descended identity. -/
theorem pointIdentity_leg (n : SimplexCategoryᵒᵖ) (j : J) (x : (K.obj j).Obj) :
    pointIdentity K n ((objectCocone K).ι.app j x) =
      (edgeCocone K n).ι.app j (identity K j n x) :=
  congrFun ((SimplicialGraph.TotalSpace.Colimit.objectIsColimit
    (graphDiagram K)).fac (identityCocone K n) j) x

/-- The descended identity has its chosen vertex as source. -/
theorem pointIdentity_source (n : SimplexCategoryᵒᵖ) :
    pointIdentity K n ≫ pointSource K n = 𝟙 (objectCocone K).pt := by
  apply (SimplicialGraph.TotalSpace.Colimit.objectIsColimit (graphDiagram K)).hom_ext
  intro j
  funext x
  change (pointIdentity K n ((objectCocone K).ι.app j x)).1 =
    (objectCocone K).ι.app j x
  rw [pointIdentity_leg]
  rfl

/-- The descended identity has its chosen vertex as target. -/
theorem pointIdentity_target (n : SimplexCategoryᵒᵖ) :
    pointIdentity K n ≫ pointTarget K n = 𝟙 (objectCocone K).pt := by
  apply (SimplicialGraph.TotalSpace.Colimit.objectIsColimit (graphDiagram K)).hom_ext
  intro j
  funext x
  change (pointIdentity K n ((objectCocone K).ι.app j x)).2.1 =
    (objectCocone K).ι.app j x
  rw [pointIdentity_leg]
  rfl

variable [IsFiltered J]

/-- Original composites form a cocone from compatible pairs into point edges. -/
noncomputable def compositionCocone (n : SimplexCategoryᵒᵖ) :
    Cocone (composableDiagram K n) where
  pt := (edgeCocone K n).pt
  ι := {
    app j e := (edgeCocone K n).ι.app j (composition K j n e)
    naturality := by
      intro i j α
      funext e
      change (edgeCocone K n).ι.app j
          (composition K j n ((composableDiagram K n).map α e)) =
        (edgeCocone K n).ι.app i (composition K i n e)
      rw [← composition_functor K α n e]
      exact congrFun ((edgeCocone K n).w α) (composition K i n e) }

/-- Composition of compatible point total edges, descended from original stages. -/
noncomputable def pointComposition (n : SimplexCategoryᵒᵖ) :
    (composableCocone K n).pt ⟶ (edgeCocone K n).pt :=
  (composableIsColimit K n).desc (compositionCocone K n)

/-- Each original composite maps to the descended composite. -/
theorem pointComposition_leg (n : SimplexCategoryᵒᵖ) (j : J)
    (e : (composableDiagram K n).obj j) :
    pointComposition K n ((composableCocone K n).ι.app j e) =
      (edgeCocone K n).ι.app j (composition K j n e) :=
  congrFun ((composableIsColimit K n).fac (compositionCocone K n) j) e

/-- The composite source is the source of the first input edge. -/
theorem pointComposition_source (n : SimplexCategoryᵒᵖ)
    (e : (composableCocone K n).pt) :
    (pointComposition K n e).1 = e.1.1.1 := by
  obtain ⟨j, x, hx⟩ := Types.jointly_surjective_of_isColimit
    (composableIsColimit K n) e
  rw [← hx, pointComposition_leg]
  calc
    ((edgeCocone K n).ι.app j (composition K j n x)).1 =
      (objectCocone K).ι.app j (composition K j n x).1 := rfl
    _ = (objectCocone K).ι.app j x.1.1.1 :=
      congrArg ((objectCocone K).ι.app j) (composition_source K j n x)
    _ = ((composableCocone K n).ι.app j x).1.1.1 := rfl

/-- The composite target is the target of the second input edge. -/
theorem pointComposition_target (n : SimplexCategoryᵒᵖ)
    (e : (composableCocone K n).pt) :
    (pointComposition K n e).2.1 = e.1.2.2.1 := by
  obtain ⟨j, x, hx⟩ := Types.jointly_surjective_of_isColimit
    (composableIsColimit K n) e
  rw [← hx, pointComposition_leg]
  calc
    ((edgeCocone K n).ι.app j (composition K j n x)).2.1 =
      (objectCocone K).ι.app j (composition K j n x).2.1 := rfl
    _ = (objectCocone K).ι.app j x.1.2.2.1 :=
      congrArg ((objectCocone K).ι.app j) (composition_target K j n x)
    _ = ((composableCocone K n).ι.app j x).1.2.2.1 := rfl

end DaggerModels.OriginalOrdinaryTotalEdgeOperations
