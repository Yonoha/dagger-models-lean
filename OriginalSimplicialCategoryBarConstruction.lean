import OriginalSimplicialCategoryOverDiagram

/-!
# The original DK80 bar construction and its original projection

The component indexed by Y is the diagonal of the degreewise nerves of C_n/Y.
The total bar is the coproduct over the unchanged original object type. Its
projection to the original diagonal nerve is induced by the native forgetful
functors, so no auxiliary model replaces the original bar or its projection.
No contraction, quasifibration, or weak-equivalence assertion is assumed.
-/
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite Simplicial DaggerModels
open DaggerOriginalSimplicialDegreeCategory
open DaggerOriginalSimplicialCategoryDiagonalNerve
open DaggerOriginalSimplicialCategoryOverDiagram
universe u
namespace DaggerOriginalSimplicialCategoryBarConstruction
noncomputable section

/-- Apply the native nerve degreewise and restrict along the native diagonal. -/
def nerveDiagonal : (SimplexCategoryᵒᵖ ⥤ Cat.{u, u}) ⥤ SSet.{u} :=
  (Functor.whiskeringRight SimplexCategoryᵒᵖ Cat.{u, u} SSet.{u}).obj nerveFunctor ⋙
    Functor.uncurry ⋙
      (Functor.whiskeringLeft SimplexCategoryᵒᵖ
        (SimplexCategoryᵒᵖ × SimplexCategoryᵒᵖ) (Type u)).obj
        (Functor.diag SimplexCategoryᵒᵖ)

/-- The original classifying complex uses the same diagonal construction. -/
theorem nerveDiagonal_original (C : SimplicialCat.{u, u}) :
    nerveDiagonal.obj (degreeCategoryDiagram C) = diagonalNerveFunctor.obj C := rfl

/-- The original DK80 bar component of chains ending in the fixed original object. -/
def barComponent (C : SimplicialCat.{u, u}) (y : C.Obj) : SSet.{u} :=
  nerveDiagonal.obj (overCategoryDiagram C y)

/-- An n-simplex is literally an n-chain in the original degree-n over category. -/
theorem barComponent_obj (C : SimplicialCat.{u, u}) (y : C.Obj)
    (n : SimplexCategoryᵒᵖ) :
    (barComponent C y).obj n = (nerve (overObjects C y n)).obj n := rfl

/-- Forget the final arrow in every original diagonal degree. -/
def barComponentProjection (C : SimplicialCat.{u, u}) (y : C.Obj) :
    barComponent C y ⟶ diagonalNerveFunctor.obj C :=
  nerveDiagonal.map (overCategoryProjection C y)

/-- The projection uses exactly the native nerve of the original forgetful functor. -/
theorem barComponentProjection_apply (C : SimplicialCat.{u, u}) (y : C.Obj)
    (n : SimplexCategoryᵒᵖ) (a : (barComponent C y).obj n) :
    (barComponentProjection C y).app n a =
      (nerveMap (Over.forget (T := degreeObjects C n) y)).app n a := rfl

/-- The whole original bar is the coproduct indexed by the original objects. -/
def bar (C : SimplicialCat.{u, u}) : SSet.{u} := ∐ (barComponent C)

/-- Include one original endpoint component in the whole original bar. -/
def barInclusion (C : SimplicialCat.{u, u}) (y : C.Obj) : barComponent C y ⟶ bar C :=
  Sigma.ι (barComponent C) y

/-- The full original bar projection, retaining every original endpoint component. -/
def barProjection (C : SimplicialCat.{u, u}) : bar C ⟶ diagonalNerveFunctor.obj C :=
  Sigma.desc (barComponentProjection C)

/-- Restriction of the full projection is the original component projection. -/
theorem barInclusion_projection (C : SimplicialCat.{u, u}) (y : C.Obj) :
    barInclusion C y ≫ barProjection C = barComponentProjection C y := by
  exact Sigma.ι_desc (barComponentProjection C) y

end
end DaggerOriginalSimplicialCategoryBarConstruction
