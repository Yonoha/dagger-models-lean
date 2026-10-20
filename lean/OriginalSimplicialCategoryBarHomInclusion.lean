import OriginalSimplicialCategoryBarFunctor

/-!
# Original Hom simplices inside the original DK80 bar component

An original arrow a : C_n(X,Y) determines the constant n-chain at a in C_n/Y.
These chains form an actual simplicial map from the unchanged original Hom to
the bar component. Their projections are exactly the constant n-chains at X.
No identification with a homotopy fibre or weak equivalence is assumed.
-/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial DaggerModels
open DaggerOriginalSimplicialDegreeCategory
open DaggerOriginalSimplicialCategoryDiagonalNerve
open DaggerOriginalSimplicialCategoryOverDiagram
open DaggerOriginalSimplicialCategoryBarConstruction
universe u
namespace DaggerOriginalSimplicialCategoryBarHomInclusion
noncomputable section

/-- A Hom simplex gives the literal constant chain at its original over object. -/
def barHomSimplex (C : SimplicialCat.{u, u}) (x y : C.Obj) (n : SimplexCategoryᵒᵖ)
    (a : (C.enriched.Hom x y).obj n) : (barComponent C y).obj n :=
  (Functor.const (Fin (n.unop.len + 1))).obj
    (Over.mk (T := degreeObjects C n) (X := y) (Y := x) a)

/-- Original Hom simplices include in the original endpoint bar component. -/
def barHomInclusion (C : SimplicialCat.{u, u}) (x y : C.Obj) :
    C.enriched.Hom x y ⟶ barComponent C y where
  app n := barHomSimplex C x y n
  naturality n m i := by
    funext a
    refine Functor.hext
      (F := barHomSimplex C x y m ((C.enriched.Hom x y).map i a))
      (G := (barComponent C y).map i (barHomSimplex C x y n a)) (fun _ ↦ rfl) ?_
    intro k l f
    exact heq_of_eq ((overDegreeMap C y i).map_id
      (Over.mk (T := degreeObjects C n) (X := y) (Y := x) a)).symm

/-- Every included simplex keeps the original Hom arrow as its final arrow. -/
theorem barHomInclusion_finalArrow (C : SimplicialCat.{u, u}) (x y : C.Obj)
    (n : SimplexCategoryᵒᵖ) (a : (C.enriched.Hom x y).obj n)
    (k : Fin (n.unop.len + 1)) :
    (((barHomInclusion C x y).app n a).obj k).hom = a := rfl

/-- The degreewise inclusion is injective on all original Hom simplices. -/
theorem barHomInclusion_injective (C : SimplicialCat.{u, u}) (x y : C.Obj)
    (n : SimplexCategoryᵒᵖ) : Function.Injective ((barHomInclusion C x y).app n) := by
  intro a b h
  have hobj := congrArg (fun s ↦ s.obj (0 : Fin (n.unop.len + 1))) h
  have hhom := congrArg (fun s ↦
    (⟨s.left, s.hom⟩ : Σ z : degreeObjects C n, (C.enriched.Hom z y).obj n)) hobj
  exact eq_of_heq (Sigma.mk.inj hhom).2

/-- Projecting the included original arrow gives the constant chain at its original source. -/
theorem barHomInclusion_projection (C : SimplicialCat.{u, u}) (x y : C.Obj)
    (n : SimplexCategoryᵒᵖ) (a : (C.enriched.Hom x y).obj n) :
    (barComponentProjection C y).app n ((barHomInclusion C x y).app n a) =
      (Functor.const (Fin (n.unop.len + 1)) (C := degreeObjects C n)).obj x := by
  refine Functor.hext
    (F := (barComponentProjection C y).app n ((barHomInclusion C x y).app n a))
    (G := (Functor.const (Fin (n.unop.len + 1)) (C := degreeObjects C n)).obj x)
    (fun _ ↦ rfl) ?_
  intro k l f
  exact heq_of_eq ((Over.forget (T := degreeObjects C n) y).map_id
    (Over.mk (T := degreeObjects C n) (X := y) (Y := x) a))

end
end DaggerOriginalSimplicialCategoryBarHomInclusion
