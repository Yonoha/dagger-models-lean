import OriginalOrdinaryTotalEdgeOperations
import OriginalOrdinaryTotalEdgeOperationsLawsStage
import OriginalOrdinaryComposableTriples

/-!
# Unit and associativity after filtered descent of total-edge operations

Each equality is checked on an actual original representative of the
appropriate Type colimit. The original enriched laws then give equality of
the descended total edges, including their endpoint labels.
-/

open CategoryTheory Limits

universe u

namespace DaggerModels.OriginalOrdinaryTotalEdgeOperations.Laws

variable {J : Type u} [SmallCategory J]
variable (K : J ⥤ SimplicialCat.{u, u})

open OriginalOrdinaryComposableEdges
open OriginalOrdinaryComposableTriples
open OriginalOrdinaryTotalEdgeOperations
open OriginalOrdinaryTotalEdgeOperations.Stage
open OriginalOrdinaryTotalEdgeOperations.LawsStage

/-- The descended identity followed by a point total edge. -/
noncomputable def pointLeftUnitPair (n : SimplexCategoryᵒᵖ)
    (e : (edgeCocone K n).pt) : (composableCocone K n).pt :=
  ⟨(pointIdentity K n e.1, e), by
    have h := congrFun (pointIdentity_target K n) e.1
    simpa only [types_comp_apply, types_id_apply] using h⟩

/-- A point total edge followed by the descended identity. -/
noncomputable def pointRightUnitPair (n : SimplexCategoryᵒᵖ)
    (e : (edgeCocone K n).pt) : (composableCocone K n).pt :=
  ⟨(e, pointIdentity K n e.2.1), by
    have h := congrFun (pointIdentity_source K n) e.2.1
    simpa only [types_comp_apply, types_id_apply] using h.symm⟩

variable [IsFiltered J]

/-- The descended composition has the chosen identity as a left unit. -/
theorem pointLeftUnit (n : SimplexCategoryᵒᵖ) (e : (edgeCocone K n).pt) :
    pointComposition K n (pointLeftUnitPair K n e) = e := by
  obtain ⟨j, x, hx⟩ := Types.jointly_surjective_of_isColimit
    (SimplicialGraph.TotalSpace.Colimit.degreeIsColimit (graphDiagram K) n) e
  rw [← hx]
  have hp : pointLeftUnitPair K n ((edgeCocone K n).ι.app j x) =
      (composableCocone K n).ι.app j (leftUnitPair K j n x) := by
    apply Subtype.ext
    apply Prod.ext
    · exact pointIdentity_leg K n j x.1
    · rfl
  calc
    pointComposition K n (pointLeftUnitPair K n ((edgeCocone K n).ι.app j x)) =
        pointComposition K n
          ((composableCocone K n).ι.app j (leftUnitPair K j n x)) := by rw [hp]
    _ = (edgeCocone K n).ι.app j (composition K j n (leftUnitPair K j n x)) :=
      pointComposition_leg K n j (leftUnitPair K j n x)
    _ = (edgeCocone K n).ι.app j x := by rw [leftUnit]

/-- The descended composition has the chosen identity as a right unit. -/
theorem pointRightUnit (n : SimplexCategoryᵒᵖ) (e : (edgeCocone K n).pt) :
    pointComposition K n (pointRightUnitPair K n e) = e := by
  obtain ⟨j, x, hx⟩ := Types.jointly_surjective_of_isColimit
    (SimplicialGraph.TotalSpace.Colimit.degreeIsColimit (graphDiagram K) n) e
  rw [← hx]
  have hp : pointRightUnitPair K n ((edgeCocone K n).ι.app j x) =
      (composableCocone K n).ι.app j (rightUnitPair K j n x) := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact pointIdentity_leg K n j x.2.1
  calc
    pointComposition K n (pointRightUnitPair K n ((edgeCocone K n).ι.app j x)) =
        pointComposition K n
          ((composableCocone K n).ι.app j (rightUnitPair K j n x)) := by rw [hp]
    _ = (edgeCocone K n).ι.app j (composition K j n (rightUnitPair K j n x)) :=
      pointComposition_leg K n j (rightUnitPair K j n x)
    _ = (edgeCocone K n).ι.app j x := by rw [rightUnit]

/-- Compose the first two point edges, then pair with the third. -/
noncomputable def pointLeftNestedPair (n : SimplexCategoryᵒᵖ)
    (e : Triple K n) : (composableCocone K n).pt :=
  ⟨(pointComposition K n e.1.1, e.1.2), by
    calc
      (pointComposition K n e.1.1).2.1 = e.1.1.1.2.2.1 :=
        pointComposition_target K n e.1.1
      _ = e.1.2.1 := e.2⟩

/-- The last two point edges as an exact compatible pair. -/
noncomputable def pointRightInnerPair (n : SimplexCategoryᵒᵖ)
    (e : Triple K n) : (composableCocone K n).pt :=
  ⟨(e.1.1.1.2, e.1.2), e.2⟩

/-- Compose the last two point edges, then pair with the first. -/
noncomputable def pointRightNestedPair (n : SimplexCategoryᵒᵖ)
    (e : Triple K n) : (composableCocone K n).pt :=
  ⟨(e.1.1.1.1, pointComposition K n (pointRightInnerPair K n e)), by
    calc
      e.1.1.1.1.2.1 = e.1.1.1.2.1 := e.1.1.2
      _ = (pointComposition K n (pointRightInnerPair K n e)).1 :=
        (pointComposition_source K n (pointRightInnerPair K n e)).symm⟩

/-- Associativity of descended composition on literal compatible triples. -/
theorem pointAssociativity (n : SimplexCategoryᵒᵖ) (e : Triple K n) :
    pointComposition K n (pointLeftNestedPair K n e) =
      pointComposition K n (pointRightNestedPair K n e) := by
  obtain ⟨j, x, hx⟩ := Types.jointly_surjective_of_isColimit
    (tripleIsColimit K n) e
  rw [← hx]
  have hl : pointLeftNestedPair K n ((tripleCocone K n).ι.app j x) =
      (composableCocone K n).ι.app j (leftNestedPair K j n x) := by
    apply Subtype.ext
    apply Prod.ext
    · change pointComposition K n
          ((composableCocone K n).ι.app j x.1.1) =
        (edgeCocone K n).ι.app j (composition K j n x.1.1)
      exact pointComposition_leg K n j x.1.1
    · rfl
  have hi : pointRightInnerPair K n ((tripleCocone K n).ι.app j x) =
      (composableCocone K n).ι.app j (rightInnerPair K j n x) := by
    apply Subtype.ext
    rfl
  have hr : pointRightNestedPair K n ((tripleCocone K n).ι.app j x) =
      (composableCocone K n).ι.app j (rightNestedPair K j n x) := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · change pointComposition K n
          (pointRightInnerPair K n ((tripleCocone K n).ι.app j x)) =
        (edgeCocone K n).ι.app j (composition K j n (rightInnerPair K j n x))
      rw [hi]
      exact pointComposition_leg K n j (rightInnerPair K j n x)
  calc
    pointComposition K n (pointLeftNestedPair K n ((tripleCocone K n).ι.app j x)) =
        (edgeCocone K n).ι.app j (composition K j n (leftNestedPair K j n x)) := by
      rw [hl, pointComposition_leg]
    _ = (edgeCocone K n).ι.app j (composition K j n (rightNestedPair K j n x)) :=
      congrArg ((edgeCocone K n).ι.app j) (associativity K j n x)
    _ = pointComposition K n
          (pointRightNestedPair K n ((tripleCocone K n).ι.app j x)) := by
      rw [hr, pointComposition_leg]

end DaggerModels.OriginalOrdinaryTotalEdgeOperations.Laws
