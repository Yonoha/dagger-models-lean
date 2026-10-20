import OriginalFixedObjectSimplicialCategories
import Mathlib.CategoryTheory.Adjunction.Evaluation
import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory
import Mathlib.CategoryTheory.Monoidal.Functor

/-! Native cofree evaluation changes the original Hom objects and keeps every object. -/
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory Opposite DaggerModels
open Functor.LaxMonoidal Functor.OplaxMonoidal
open DaggerOriginalFixedObjectSimplicialCategories DaggerOriginalSimplicialDegreeCategory
universe u
namespace DaggerOriginalDegreeCofreeEnrichment
noncomputable section

abbrev eval (n : SimplexCategoryᵒᵖ) : SSet.{u} ⥤ Type u :=
  (evaluation SimplexCategoryᵒᵖ (Type u)).obj n

abbrev cofree (n : SimplexCategoryᵒᵖ) : Type u ⥤ SSet.{u} :=
  evaluationRightAdjoint.{0, u, 0, u + 1} (Type u) n

def evalOplax (n : SimplexCategoryᵒᵖ) : (eval.{u} n).OplaxMonoidal :=
  Functor.OplaxMonoidal.ofChosenFiniteProducts _

attribute [local instance] evalOplax

def cofreeLax (n : SimplexCategoryᵒᵖ) : (cofree.{u} n).LaxMonoidal := by
  letI := evalOplax.{u} n
  exact (evaluationAdjunctionLeft.{0, u, 0, u + 1} (Type u) n).rightAdjointLaxMonoidal

attribute [local instance] cofreeLax

theorem eval_delta (n : SimplexCategoryᵒᵖ) (X Y : SSet.{u}) :
    δ (eval n) X Y = 𝟙 ((eval n).obj X ⊗ (eval n).obj Y) := by
  rfl

/-- Mathlib transports all enriched category laws along the actual right adjoint. -/
def cofreeCategory (n : SimplexCategoryᵒᵖ) (D : Type u) [Category.{u} D] :
    SimplicialCat.{u, u} := by
  letI := enrichedCategoryTypeOfCategory D
  exact ⟨D, inferInstanceAs
    (EnrichedCategory SSet.{u} (TransportEnrichment (cofree.{u} n) D))⟩

theorem cofreeCategory_obj (n : SimplexCategoryᵒᵖ) (D : Type u) [Category.{u} D] :
    (cofreeCategory n D).Obj = D := rfl

theorem cofreeCategory_hom (n : SimplexCategoryᵒᵖ) (D : Type u) [Category.{u} D]
    (x y : D) : (cofreeCategory n D).enriched.Hom x y = (cofree.{u} n).obj (x ⟶ y) := rfl

end
end DaggerOriginalDegreeCofreeEnrichment
