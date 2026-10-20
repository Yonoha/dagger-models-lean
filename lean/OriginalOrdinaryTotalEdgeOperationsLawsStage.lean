import OriginalOrdinaryTotalEdgeOperationsStage
import OriginalOrdinaryComposableTriples

/-!
# Original degreewise unit and associativity laws on total edges

These are the existing enriched-category laws on the original diagram,
expressed on total edges with all object labels retained. They provide the
stagewise equalities used to descend the laws to the filtered graph colimit.
-/

open CategoryTheory MonoidalCategory

universe u

namespace DaggerModels.OriginalOrdinaryTotalEdgeOperations.LawsStage

variable {J : Type u} [SmallCategory J]
variable (K : J ⥤ SimplicialCat.{u, u})

open OriginalOrdinaryComposableEdges
open OriginalOrdinaryTotalEdgeOperations.Stage
open OriginalOrdinaryComposableTriples

/-- An original identity followed by an original total edge. -/
def leftUnitPair (j : J) (n : SimplexCategoryᵒᵖ)
    (e : (edgeDegreeDiagram K n).obj j) : (composableDiagram K n).obj j :=
  ⟨(identity K j n e.1, e), rfl⟩

/-- An original total edge followed by an original identity. -/
def rightUnitPair (j : J) (n : SimplexCategoryᵒᵖ)
    (e : (edgeDegreeDiagram K n).obj j) : (composableDiagram K n).obj j :=
  ⟨(e, identity K j n e.2.1), rfl⟩

/-- The actual original enriched left unit law, including endpoint labels. -/
theorem leftUnit (j : J) (n : SimplexCategoryᵒᵖ)
    (e : (edgeDegreeDiagram K n).obj j) :
    composition K j n (leftUnitPair K j n e) = e := by
  rcases e with ⟨x, y, f⟩
  exact congrArg (fun t ↦ (⟨x, y, t⟩ : (edgeDegreeDiagram K n).obj j))
    (congrFun (NatTrans.congr_app
      (e_id_comp SSet (show (K.obj j).Obj from x) y) n) f)

/-- The actual original enriched right unit law, including endpoint labels. -/
theorem rightUnit (j : J) (n : SimplexCategoryᵒᵖ)
    (e : (edgeDegreeDiagram K n).obj j) :
    composition K j n (rightUnitPair K j n e) = e := by
  rcases e with ⟨x, y, f⟩
  exact congrArg (fun t ↦ (⟨x, y, t⟩ : (edgeDegreeDiagram K n).obj j))
    (congrFun (NatTrans.congr_app
      (e_comp_id SSet (show (K.obj j).Obj from x) y) n) f)

/-- First compose the first two edges, then pair with the third. -/
def leftNestedPair (j : J) (n : SimplexCategoryᵒᵖ)
    (x : (tripleDiagram K n).obj j) : (composableDiagram K n).obj j :=
  ⟨(composition K j n x.1.1, x.1.2), by
    calc
      (composition K j n x.1.1).2.1 = x.1.1.1.2.2.1 :=
        composition_target K j n x.1.1
      _ = x.1.2.1 := x.2⟩

/-- The second and third original edges as a compatible pair. -/
def rightInnerPair (j : J) (n : SimplexCategoryᵒᵖ)
    (x : (tripleDiagram K n).obj j) : (composableDiagram K n).obj j :=
  ⟨(x.1.1.1.2, x.1.2), x.2⟩

/-- First compose the last two edges, then pair with the first. -/
def rightNestedPair (j : J) (n : SimplexCategoryᵒᵖ)
    (x : (tripleDiagram K n).obj j) : (composableDiagram K n).obj j :=
  ⟨(x.1.1.1.1, composition K j n (rightInnerPair K j n x)), by
    calc
      x.1.1.1.1.2.1 = x.1.1.1.2.1 := x.1.1.2
      _ = (composition K j n (rightInnerPair K j n x)).1 :=
        (composition_source K j n (rightInnerPair K j n x)).symm⟩

/-- The actual original enriched associativity law on three total edges. -/
theorem associativity (j : J) (n : SimplexCategoryᵒᵖ)
    (x : (tripleDiagram K n).obj j) :
    composition K j n (leftNestedPair K j n x) =
      composition K j n (rightNestedPair K j n x) := by
  rcases x with
    ⟨⟨⟨⟨⟨w, x, f⟩, ⟨x', y, g⟩⟩, h₁⟩, ⟨y', z, h⟩⟩, h₂⟩
  change x = x' at h₁
  subst x'
  change y = y' at h₂
  subst y'
  exact congrArg (fun t ↦ (⟨w, z, t⟩ : (edgeDegreeDiagram K n).obj j))
    (congrFun (NatTrans.congr_app
      (e_assoc SSet (show (K.obj j).Obj from w) x y z) n) (f, g, h))

end DaggerModels.OriginalOrdinaryTotalEdgeOperations.LawsStage
