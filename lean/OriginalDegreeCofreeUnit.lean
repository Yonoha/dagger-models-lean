import OriginalDegreeCofreeEnrichment

/-! The actual evaluation unit lifts the same original degree category on all Hom maps. -/
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory Opposite DaggerModels
open Functor.LaxMonoidal Functor.OplaxMonoidal
open DaggerOriginalDegreeCofreeEnrichment DaggerOriginalSimplicialDegreeCategory
universe u
namespace DaggerOriginalDegreeCofreeUnit
noncomputable section
attribute [local instance] evalOplax cofreeLax

def degreeUnit (C : SimplicialCat.{u, u}) (n : SimplexCategoryᵒᵖ) :
    C ⟶ cofreeCategory n (degreeObjects C n) where
  obj x := x
  map x y := (evaluationAdjunctionLeft (Type u) n).unit.app (C.enriched.Hom x y)
  map_id x := by
    letI := evalOplax.{u} n
    letI := cofreeLax.{u} n
    let a := evaluationAdjunctionLeft.{0, u, 0, u + 1} (Type u) n
    change C.enriched.id x ≫ a.unit.app _ = ε (cofree n) ≫ (cofree n).map _
    have hn := a.unit.naturality (C.enriched.id x)
    change C.enriched.id x ≫ a.unit.app _ =
      a.unit.app _ ≫ (cofree n).map ((eval n).map (C.enriched.id x)) at hn
    rw [hn]
    have ht := a.unit_app_unit_comp_map_η
    change a.unit.app _ ≫ (cofree n).map (η (eval n)) = ε (cofree n) at ht
    rw [← ht, Category.assoc, ← Functor.map_comp]
    congr 1
  map_comp x y z := by
    letI := evalOplax.{u} n
    letI := cofreeLax.{u} n
    let a := evaluationAdjunctionLeft.{0, u, 0, u + 1} (Type u) n
    change C.enriched.comp x y z ≫ a.unit.app _ =
      (a.unit.app _ ⊗ₘ a.unit.app _) ≫ μ (cofree n) _ _ ≫ (cofree n).map _
    have hn := a.unit.naturality (C.enriched.comp x y z)
    change C.enriched.comp x y z ≫ a.unit.app _ =
      a.unit.app _ ≫ (cofree n).map ((eval n).map (C.enriched.comp x y z)) at hn
    rw [hn]
    have ht := a.unit_app_tensor_comp_map_δ (C.enriched.Hom x y) (C.enriched.Hom y z)
    change a.unit.app _ ≫ (cofree n).map (δ (eval n) _ _) =
      (a.unit.app _ ⊗ₘ a.unit.app _) ≫ μ (cofree n) _ _ at ht
    rw [← Category.assoc, ← ht, Category.assoc, ← Functor.map_comp]
    congr 1

/-- The Hom map is the unchanged native unit, not merely a pointwise equivalent map. -/
theorem degreeUnit_hom (C : SimplicialCat.{u, u}) (n : SimplexCategoryᵒᵖ) (x y : C.Obj) :
    (degreeUnit C n).map x y =
      (evaluationAdjunctionLeft (Type u) n).unit.app (C.enriched.Hom x y) := rfl

end
end DaggerOriginalDegreeCofreeUnit
