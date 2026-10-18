import OriginalSimplicialCategoryBarBidegreeDecomposition

/-!
# The full original bar and base with horizontal chain degree fixed

Flip the native bisimplicial nerves; every resulting row is a simplicial set
in the original enrichment degree. Its diagonal is the already constructed
original bar. Horizontal maps remain the native nerve restriction maps.
-/
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite Simplicial DaggerModels
open DaggerOriginalSimplicialDegreeCategory DaggerOriginalSimplicialCategoryOverDiagram
open DaggerOriginalSimplicialCategoryDiagonalNerve DaggerOriginalSimplicialCategoryBarConstruction
universe u
namespace DaggerOriginalSimplicialCategoryBarRows
noncomputable section

/-- The original endpoint bar before taking its actual native diagonal. -/
def barBisimplicial (C : SimplicialCat.{u, u}) (z : C.Obj) :
    SimplexCategoryᵒᵖ ⥤ SSet.{u} :=
  (Functor.whiskeringRight SimplexCategoryᵒᵖ Cat.{u, u} SSet.{u}).obj nerveFunctor |>.obj
    (overCategoryDiagram C z)

/-- All native horizontal rows of the same original endpoint bar. -/
def barRows (C : SimplicialCat.{u, u}) (z : C.Obj) : SimplexCategoryᵒᵖ ⥤ SSet.{u} :=
  (barBisimplicial C z).flip

/-- All native horizontal rows of the same original base nerve. -/
def baseRows (C : SimplicialCat.{u, u}) : SimplexCategoryᵒᵖ ⥤ SSet.{u} :=
  (bisimplicialNerveFunctor.obj C).flip

/-- The fixed horizontal row retains every original vertical simplicial operator. -/
abbrev barRow (C : SimplicialCat.{u, u}) (z : C.Obj) (k : ℕ) : SSet.{u} :=
  (barRows C z).obj (op ⦋k⦌)

/-- The base row retains the actual whole k-chain in every original enrichment degree. -/
abbrev baseRow (C : SimplicialCat.{u, u}) (k : ℕ) : SSet.{u} :=
  (baseRows C).obj (op ⦋k⦌)

/-- Projection is the actual native forgetful functor on the entire original chain. -/
def rowProjection (C : SimplicialCat.{u, u}) (z : C.Obj) (k : ℕ) :
    barRow C z k ⟶ baseRow C k where
  app v := (nerveMap (Over.forget (T := degreeObjects C v) z)).app (op ⦋k⦌)
  naturality v w i := by
    funext B
    change (B ⋙ overDegreeMap C z i) ⋙ Over.forget (T := degreeObjects C w) z =
      (B ⋙ Over.forget (T := degreeObjects C v) z) ⋙ degreeMap C i
    rw [Functor.assoc, overDegreeMap_forget]
    rfl

/-- Every original horizontal restriction commutes with the full original projection. -/
theorem rowProjection_horizontal (C : SimplicialCat.{u, u}) (z : C.Obj) {k l : ℕ}
    (α : ⦋l⦌ ⟶ ⦋k⦌) :
    (barRows C z).map α.op ≫ rowProjection C z l =
      rowProjection C z k ≫ (baseRows C).map α.op := by
  apply NatTrans.ext
  funext v B
  rfl

/-- The diagonal degree of the original bar is the same-degree original row. -/
theorem barRow_diagonal_obj (C : SimplicialCat.{u, u}) (z : C.Obj)
    (v : SimplexCategoryᵒᵖ) :
    (barRow C z v.unop.len).obj v = (barComponent C z).obj v := rfl

/-- Its same-degree row projection is the actual original diagonal projection. -/
theorem rowProjection_diagonal_app (C : SimplicialCat.{u, u}) (z : C.Obj)
    (v : SimplexCategoryᵒᵖ) :
    (rowProjection C z v.unop.len).app v = (barComponentProjection C z).app v := rfl

end
end DaggerOriginalSimplicialCategoryBarRows
