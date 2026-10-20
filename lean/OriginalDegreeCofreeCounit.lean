import OriginalDegreeCofreeUnit
import OriginalDegreeCofreeMaps

/-! Evaluation at the same degree recovers the native category and its actual unit. -/
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory Opposite DaggerModels
open Functor.LaxMonoidal Functor.OplaxMonoidal
open DaggerOriginalDegreeCofreeEnrichment DaggerOriginalSimplicialDegreeCategory
open DaggerOriginalDegreeCofreeUnit DaggerOriginalDegreeCofreeMaps
universe u
namespace DaggerOriginalDegreeCofreeCounit
noncomputable section
attribute [local instance] evalOplax cofreeLax

def degreeCounit (n : SimplexCategoryᵒᵖ) (D : Type u) [Category.{u} D] :
    degreeObjects (cofreeCategory n D) n ⥤ D where
  obj x := x
  map {x y : D} f := (evaluationAdjunctionLeft (Type u) n).counit.app (x ⟶ y) f
  map_id (x : D) := by
    letI := enrichedCategoryTypeOfCategory D
    letI := evalOplax.{u} n
    letI := cofreeLax.{u} n
    let a := evaluationAdjunctionLeft.{0, u, 0, u + 1} (Type u) n
    have h := a.counit.naturality (eId (Type u) x)
    change (eval n).map ((cofree n).map (eId (Type u) x)) ≫ a.counit.app (x ⟶ x) =
      a.counit.app PUnit.{u + 1} ≫ eId (Type u) x at h
    have he := a.map_ε_comp_counit_app_unit
    change (eval n).map (ε (cofree n)) ≫ a.counit.app PUnit.{u + 1} = η (eval n) at he
    have ht : (eval n).map (ε (cofree n) ≫ (cofree n).map (eId (Type u) x)) ≫
        a.counit.app (x ⟶ x) = η (eval n) ≫ eId (Type u) x := by
      rw [Functor.map_comp, Category.assoc, h, ← Category.assoc, he]
    exact congr_fun ht PUnit.unit
  map_comp {x y z : D} f g := by
    letI := enrichedCategoryTypeOfCategory D
    letI := evalOplax.{u} n
    letI := cofreeLax.{u} n
    let a := evaluationAdjunctionLeft.{0, u, 0, u + 1} (Type u) n
    have h := a.counit.naturality (eComp (Type u) x y z)
    change (eval n).map ((cofree n).map (eComp (Type u) x y z)) ≫
      a.counit.app (x ⟶ z) = a.counit.app ((x ⟶ y) × (y ⟶ z)) ≫ eComp (Type u) x y z at h
    have hm := a.map_μ_comp_counit_app_tensor (x ⟶ y) (y ⟶ z)
    change (eval n).map (μ (cofree n) (x ⟶ y) (y ⟶ z)) ≫
      a.counit.app ((x ⟶ y) × (y ⟶ z)) =
        δ (eval n) _ _ ≫ (a.counit.app (x ⟶ y) ⊗ₘ a.counit.app (y ⟶ z)) at hm
    have ht : (eval n).map (μ (cofree n) _ _ ≫
        (cofree n).map (eComp (Type u) x y z)) ≫ a.counit.app (x ⟶ z) =
        δ (eval n) _ _ ≫ (a.counit.app (x ⟶ y) ⊗ₘ a.counit.app (y ⟶ z)) ≫
          eComp (Type u) x y z := by
      change (eval n).map (μ (cofree n) (x ⟶ y) (y ⟶ z) ≫
        (cofree n).map (eComp (Type u) x y z)) ≫ a.counit.app (x ⟶ z) =
          δ (eval n) ((cofree n).obj (x ⟶ y)) ((cofree n).obj (y ⟶ z)) ≫
            (a.counit.app (x ⟶ y) ⊗ₘ a.counit.app (y ⟶ z)) ≫ eComp (Type u) x y z
      rw [Functor.map_comp, Category.assoc, h, ← Category.assoc, hm, Category.assoc]
    exact congr_fun ht (f, g)

theorem degreeUnit_counit (C : SimplicialCat.{u, u}) (n : SimplexCategoryᵒᵖ) :
    degreeFunctor (degreeUnit C n) n ⋙ degreeCounit n (degreeObjects C n) =
      𝟭 (degreeObjects C n) := by
  refine CategoryTheory.Functor.ext (fun x ↦ rfl) ?_
  intro x y f
  have h := (evaluationAdjunctionLeft (Type u) n).left_triangle_components
    (C.enriched.Hom x y)
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  exact congr_fun h f

theorem degreeCounit_naturality (n : SimplexCategoryᵒᵖ) {D E : Type u}
    [Category.{u} D] [Category.{u} E] (F : D ⥤ E) :
    degreeFunctor (cofreeMap n F) n ⋙ degreeCounit n E = degreeCounit n D ⋙ F := by
  refine CategoryTheory.Functor.ext (fun x ↦ rfl) ?_
  intro x y f
  let x' : D := x
  let y' : D := y
  have h := (evaluationAdjunctionLeft (Type u) n).counit.naturality
    (show (x' ⟶ y') ⟶ (F.obj x' ⟶ F.obj y') from fun a ↦ F.map a)
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  exact congr_fun h f

end
end DaggerOriginalDegreeCofreeCounit
