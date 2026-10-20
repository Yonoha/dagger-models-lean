import NativeDaggerObjectRestriction
import ActualIsomorphismPartLocalWeakInvariance

/-! The literal original restriction inclusion is identity on every selected Hom.
It reflects ALL original isomorphism-component membership, even for repeated labels.
-/
set_option autoImplicit false
open CategoryTheory DaggerModels HomotopicalAlgebra
open DaggerOriginalFixedObjectDaggerCategories DaggerNativeDaggerObjectRestriction
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeDaggerRestrictionInclusion
noncomputable section

def inclusion {O : Type u} (D : DaggerSimplicialCat.{u, u}) (θ : O → D.Obj) :
    originalDagger (restriction D θ) ⟶ D where
  obj := θ
  map := fun _ _ ↦ 𝟙 _
  map_id := fun _ ↦ by rfl
  map_comp := fun _ _ _ ↦ by rfl
  map_dagger := fun _ _ ↦ by rfl

theorem hom_weak {O : Type u} (D : DaggerSimplicialCat.{u, u}) (θ : O → D.Obj) (i j : O) :
    WeakEquivalence ((inclusion D θ).map i j) := by
  change WeakEquivalence (𝟙 (D.enriched.Hom (θ i) (θ j)))
  infer_instance

theorem part_mem_iff {O : Type u} (D : DaggerSimplicialCat.{u, u}) (θ : O → D.Obj)
    (i j : O) (q : SimplexCategoryᵒᵖ) (s : (D.enriched.Hom (θ i) (θ j)).obj q) :
    s ∈ (DaggerActualSimplicialIsomorphismComponentPart.homSubcomplex
      (originalDagger (restriction D θ)).toSimplicialCat i j).obj q ↔
    s ∈ (DaggerActualSimplicialIsomorphismComponentPart.homSubcomplex
      D.toSimplicialCat (θ i) (θ j)).obj q :=
  DaggerActualIsomorphismPartLocalWeakInvariance.mem_iff
    (inclusion D θ).toEnrichedFunctor (hom_weak D θ) i j q s

end
end DaggerNativeDaggerRestrictionInclusion
