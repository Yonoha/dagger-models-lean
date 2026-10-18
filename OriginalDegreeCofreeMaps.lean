import OriginalDegreeCofreeEnrichment
import NativeDegreeEvaluationTrivialFibrations

/-! Whole ordinary functors give native cofree maps with the same objects and Hom maps. -/
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory Opposite HomotopicalAlgebra DaggerModels
open Functor.LaxMonoidal
open DaggerOriginalDegreeCofreeEnrichment DaggerNativeDegreeEvaluationTrivialFibrations
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerOriginalDegreeCofreeMaps
noncomputable section
attribute [local instance] evalOplax cofreeLax

def cofreeMap (n : SimplexCategoryᵒᵖ) {D E : Type u} [Category.{u} D] [Category.{u} E]
    (F : D ⥤ E) : cofreeCategory n D ⟶ cofreeCategory n E where
  obj := F.obj
  map (x : D) (y : D) := (cofree n).map (fun f : x ⟶ y ↦ F.map f)
  map_id (x : D) := by
    change (ε (cofree n) ≫ (cofree n).map _) ≫ (cofree n).map _ =
      ε (cofree n) ≫ (cofree n).map _
    rw [Category.assoc, ← Functor.map_comp]
    congr 1
    apply congrArg (cofree n).map
    funext p
    exact F.map_id x
  map_comp (x : D) (y : D) (z : D) := by
    change (μ (cofree n) _ _ ≫ (cofree n).map _) ≫ (cofree n).map _ =
      ((cofree n).map _ ⊗ₘ (cofree n).map _) ≫
        μ (cofree n) _ _ ≫ (cofree n).map _
    let fxy : (x ⟶ y) ⟶ (F.obj x ⟶ F.obj y) := fun f ↦ F.map f
    let fyz : (y ⟶ z) ⟶ (F.obj y ⟶ F.obj z) := fun f ↦ F.map f
    let fxz : (x ⟶ z) ⟶ (F.obj x ⟶ F.obj z) := fun f ↦ F.map f
    let cD : ((x ⟶ y) × (y ⟶ z)) ⟶ (x ⟶ z) := fun p ↦ p.1 ≫ p.2
    let cE : ((F.obj x ⟶ F.obj y) × (F.obj y ⟶ F.obj z)) ⟶ (F.obj x ⟶ F.obj z) :=
      fun p ↦ p.1 ≫ p.2
    have hc : cD ≫ fxz = (fxy ⊗ₘ fyz) ≫ cE := by
      funext p
      exact F.map_comp p.1 p.2
    rw [Category.assoc, ← Functor.map_comp]
    change μ (cofree n) _ _ ≫ (cofree n).map (cD ≫ fxz) =
      ((cofree n).map fxy ⊗ₘ (cofree n).map fyz) ≫ μ (cofree n) _ _ ≫ (cofree n).map cE
    rw [hc, Functor.map_comp, Functor.LaxMonoidal.μ_natural_assoc]

theorem cofreeMap_hom (n : SimplexCategoryᵒᵖ) {D E : Type u}
    [Category.{u} D] [Category.{u} E] (F : D ⥤ E) (x y : D) :
    (cofreeMap n F).map x y = (cofree n).map (fun f : x ⟶ y ↦ F.map f) := rfl

/-- Full surjectivity is tested on every original Hom, keeping the actual native map. -/
theorem cofreeMap_hom_trivialFibration (n : SimplexCategoryᵒᵖ) {D E : Type u}
    [Category.{u} D] [Category.{u} E] (F : D ⥤ E)
    (hF : ∀ x y : D, Function.Surjective (fun f : x ⟶ y ↦ F.map f)) (x y : D) :
    trivialFibrations SSet.{u} ((cofreeMap n F).map x y) :=
  evaluationRightAdjoint_trivialFibration n _ (hF x y)

end
end DaggerOriginalDegreeCofreeMaps
