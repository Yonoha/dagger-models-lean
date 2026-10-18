import OriginalFixedObjectDaggerColimits
import OriginalFixedObjectAmbientDaggerModel

/-! Restrict original dagger categories along arbitrary labelled object functions. -/
set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra DaggerModels
open DaggerOriginalFixedObjectSimplicialCategories DaggerOriginalFixedObjectDaggerCategories
open DaggerOriginalFixedObjectLegacyDaggerEquivalence
open scoped SSet.modelCategoryQuillen DaggerOriginalFixedObjectAmbientDaggerModel
universe u
namespace DaggerNativeDaggerObjectRestriction
noncomputable section

def restriction {O : Type u} (D : DaggerSimplicialCat.{u, u}) (θ : O → D.Obj) :
    FixedDaggerCategory O :=
  fromLegacyObject (DaggerFixedCategoryConnectedColimits.reindex D θ)

def map {O : Type u} {D E : DaggerSimplicialCat.{u, u}} (F : D ⟶ E)
    (θ : O → D.Obj) : restriction D θ ⟶ restriction E (F.obj ∘ θ) where
  underlying :=
    { map := fun i j ↦ F.map (θ i) (θ j)
      map_id := fun i ↦ F.map_id (θ i)
      map_comp := fun i j k ↦ F.map_comp (θ i) (θ j) (θ k) }
  map_dagger := fun i j ↦ F.map_dagger (θ i) (θ j)

theorem map_hom {O : Type u} {D E : DaggerSimplicialCat.{u, u}} (F : D ⟶ E)
    (θ : O → D.Obj) (i j : O) : (map F θ).underlying.map i j = F.map (θ i) (θ j) :=
  rfl

theorem map_id {O : Type u} (D : DaggerSimplicialCat.{u, u}) (θ : O → D.Obj) :
    map (𝟙 D) θ = 𝟙 (restriction D θ) := by
  apply fixedDaggerHom_ext
  apply fixedHom_ext
  intro i j
  rfl

theorem map_comp {O : Type u} {D E K : DaggerSimplicialCat.{u, u}}
    (F : D ⟶ E) (G : E ⟶ K) (θ : O → D.Obj) :
    map (F ≫ G) θ = map F θ ≫ map G (F.obj ∘ θ) := by
  apply fixedDaggerHom_ext
  apply fixedHom_ext
  intro i j
  rfl

theorem map_weak {O : Type u} {D E : DaggerSimplicialCat.{u, u}} (F : D ⟶ E)
    (θ : O → D.Obj) (h : ∀ x y : D.Obj, WeakEquivalence (F.map x y)) :
    WeakEquivalence (map F θ) := by
  rw [DaggerOriginalFixedObjectAmbientDaggerModel.weakEquivalence_iff_original]
  intro i j
  exact h (θ i) (θ j)

end
end DaggerNativeDaggerObjectRestriction
